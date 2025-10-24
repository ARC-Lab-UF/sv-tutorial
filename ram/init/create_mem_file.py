#!/usr/bin/env python3
# MIT License
# Copyright (c) 2025 Gregory Stitt
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# Greg Stitt
# StittHub (www.stitt-hub.com)
# See articles:
# https://stitt-hub.com/portable-ram-inference-templates-for-fpgas/
# https://stitt-hub.com/fpga-ram-inference-templates-part-2/

# Note: Generated code has not been tested in the non-pro versions of Quartus.
# SystemVerilog support is not great in those versions, so I have abandoned
# trying to support it.

import argparse
import sys
import yaml
import random
from os.path import splitext
from collections import Counter


# ------------------------------------------------------------
# Utility helpers
# ------------------------------------------------------------


def hex_digits_required(width):
    """Return number of hex digits needed to represent a width-bit value."""
    return (width + 3) // 4


def most_frequent_value(values):
    """Return the most frequent value in a list (or None for empty)."""
    return Counter(values).most_common(1)[0][0] if values else None


def compute_identical_ranges(values):
    """
    Convert a list into (start, end, value) ranges where identical
    adjacent values are collapsed.
    """
    if not values:
        return []

    ranges = []
    start = 0
    prev = values[0]

    for i in range(1, len(values)):
        if values[i] != prev:
            ranges.append((start, i - 1, prev))
            start = i
            prev = values[i]

    ranges.append((start, len(values) - 1, prev))
    return ranges


# ------------------------------------------------------------
# Formatting helpers for SV/VHDL literals
# ------------------------------------------------------------


def sv_format_value(val, base="hex"):
    if base == "hex":
        return f"'h{val:X}"
    if base == "dec":
        return str(val)
    if base == "bin":
        return f"'b{val:b}"
    raise ValueError(f"Unsupported SV base: {base}")


def vhdl_format_value(val, width, base="hex"):
    """Format a VHDL literal."""
    if base == "hex":
        return f'x"{val:0{hex_digits_required(width)}X}"'
    if base == "dec":
        return f"std_logic_vector(to_unsigned({val}, {width}))"
    if base == "bin":
        return f'"{val:b}"'
    raise ValueError(f"Unsupported VHDL base: {base}")


# ------------------------------------------------------------
# Assignment helpers
# ------------------------------------------------------------


def warn_if_overwritten(defined, addr, source):
    if defined[addr]:
        print(f"Warning: address {addr} overwritten by {source}")


def assign(memory, defined, addr, value, source, warn=False):
    """Unified assignment that handles warnings."""
    if warn:
        warn_if_overwritten(defined, addr, source)
    defined[addr] = True
    memory[addr] = value


def get_int(x):
    return int(x, 0) if isinstance(x, str) else int(x)


# ------------------------------------------------------------
# SV and VHDL generation
# ------------------------------------------------------------


def create_sv_array_literal(values, most_frequent, indent="    ", base="hex"):
    """Create SV array literal using explicit indices + default."""
    lines = [f"{indent}'{{"]
    inner = indent * 2

    for i, val in enumerate(values):
        if val != most_frequent:
            lines.append(f"{inner}{i}: {sv_format_value(val, base)},")

    lines.append(f"{inner}default: {sv_format_value(most_frequent, base)}")
    lines.append(f"{indent}}}")
    return "\n".join(lines)


def create_sv_package(
    pkg_name, array_name, sv_type, size, values, most_frequent, base="hex"
):
    literal = create_sv_array_literal(values, most_frequent, base=base)
    return f"""
package {pkg_name};

    localparam {sv_type} {array_name}[{size}] =
{literal};

endpackage
""".lstrip()


def create_vhdl_array_literal(ranges, width, indent="    ", base="hex"):
    """Generate VHDL array literal with ranges and default/compressed entries."""
    slice_suffix = "" if (width % 4 == 0 or base != "hex") else f"({width-1} downto 0)"
    inner = indent * 2

    lines = [f"{indent}("]
    for i, (start, end, val) in enumerate(ranges):
        val_str = vhdl_format_value(val, width, base)
        comma = "," if i < len(ranges) - 1 else ""
        if start == end:
            lines.append(f"{inner}{start} => {val_str}{slice_suffix}{comma}")
        else:
            lines.append(f"{inner}{start} to {end} => {val_str}{slice_suffix}{comma}")

    lines.append(f"{indent})")
    return "\n".join(lines)


def create_vhdl_package(pkg_name, array_name, width, ranges, base="hex"):
    literal = create_vhdl_array_literal(ranges, width, base=base)
    size = sum(end - start + 1 for start, end, _ in ranges)

    return f"""
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package {pkg_name} is

    constant C_NUM_ELEMENTS  : integer := {size};
    constant C_ELEMENT_WIDTH : integer := {width};
    constant C_TOTAL_BITS    : integer := C_NUM_ELEMENTS*C_ELEMENT_WIDTH;
    type {array_name}_t is array(0 to C_NUM_ELEMENTS-1) of std_logic_vector(C_ELEMENT_WIDTH-1 downto 0);

    -- Automatically generated constant array
    constant {array_name.upper()} : {array_name}_t :=
{literal};

    -- Convert array to SLV (for VHDL-93)
    function to_slv(a : {array_name}_t) return std_logic_vector;

    constant {array_name.upper()}_SLV : std_logic_vector(C_TOTAL_BITS-1 downto 0) := to_slv({array_name.upper()});

end package {pkg_name};

package body {pkg_name} is

    function to_slv(a : {array_name}_t) return std_logic_vector is
        variable result : std_logic_vector(C_TOTAL_BITS-1 downto 0);
    begin
        for i in a'range loop
            result((i+1)*C_ELEMENT_WIDTH-1 downto i*C_ELEMENT_WIDTH) := a(i);
        end loop;
        return result;
    end function;

end package body {pkg_name};
""".lstrip()


# ------------------------------------------------------------
# YAML parsing + generation
# ------------------------------------------------------------


def require(config, key):
    """Ensure YAML contains required key."""
    if key not in config:
        raise ValueError(f"'{key}' is required in YAML configuration.")
    return config[key]


def build_pattern_generator(entry, width):
    """Return a function i -> value for a pattern entry."""
    if "fill" in entry:
        value = get_int(entry["fill"])
        return lambda i: value

    if "seq_start" in entry:
        start = get_int(entry["seq_start"])
        step = entry.get("seq_step", 1)
        return lambda i: start + i * step

    if "repeat" in entry:
        pattern = [get_int(v) for v in entry["repeat"]]
        return lambda i: pattern[i % len(pattern)]

    if "random" in entry:
        cfg = entry["random"]
        if "seed" in cfg:
            random.seed(cfg["seed"])
        rmin = get_int(cfg.get("min", 0))
        rmax = get_int(cfg.get("max", (1 << width) - 1))
        return lambda i: random.randint(rmin, rmax)

    raise ValueError(f"Unknown pattern type: {entry}")


def parse_memory_init(
    yaml_file, mem_file, sv_file, vhdl_file, pkg_name, array_name, enable_warnings=False
):
    """Parse YAML config and generate memory/SV/VHDL outputs."""

    with open(yaml_file, "r") as f:
        config = yaml.safe_load(f)

    width = require(config, "width")
    depth = require(config, "depth")
    default = get_int(config.get("default", 0))

    memory = [default] * depth
    defined = [False] * depth

    # Apply pattern-based sections
    for entry in config.get("patterns", []):
        if (
            "range" not in entry
            or not isinstance(entry["range"], list)
            or len(entry["range"]) != 2
        ):
            raise ValueError(f"Invalid range: {entry}")

        start, end = entry["range"]
        if start > end:
            raise ValueError(f"Range start {hex(start)} > end {hex(end)}")

        gen = build_pattern_generator(entry, width)

        for i, addr in enumerate(range(start, end + 1)):
            assign(memory, defined, addr, gen(i), entry, enable_warnings)

    # Explicit values override patterns
    for addr, value in config.get("values", {}).items():
        val = get_int(value)
        assign(memory, defined, addr, val, f"value {hex(val)}", enable_warnings)

    # Write .mem
    if mem_file:
        digits = hex_digits_required(width)
        with open(mem_file, "w") as f:
            for value in memory:
                f.write(f"{value:0{digits}X}\n")

    # Write SystemVerilog package
    if sv_file:
        most_frequent = most_frequent_value(memory)
        pkg = create_sv_package(
            pkg_name,
            array_name.upper(),
            f"logic [{width-1}:0]",
            len(memory),
            memory,
            most_frequent,
        )
        with open(sv_file, "w") as f:
            f.write(pkg)

    # Write VHDL package
    if vhdl_file:
        ranges = compute_identical_ranges(memory)
        pkg = create_vhdl_package(pkg_name, array_name, width, ranges)
        with open(vhdl_file, "w") as f:
            f.write(pkg)


# ------------------------------------------------------------
# CLI
# ------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Generate RAM initialization and HDL packages from YAML"
    )

    parser.add_argument("yaml_file", type=str)
    parser.add_argument("--mem", type=str, help="Memory output file (.mem format)")
    parser.add_argument("--sv", type=str, help="SystemVerilog output file")
    parser.add_argument("--vhdl", type=str, help="VHDL output file")
    parser.add_argument(
        "--pkg", type=str, help="Package name (default: YAML filename + _pkg)"
    )
    parser.add_argument(
        "--array", type=str, help="Array name (default: YAML filename + _array)"
    )
    parser.add_argument(
        "-w", "--warning", action="store_true", help="Enable overwrite warnings"
    )

    args = parser.parse_args()

    if not any([args.mem, args.sv, args.vhdl]):
        print("Error: No output file defined.", file=sys.stderr)
        sys.exit(1)

    base = splitext(args.yaml_file)[0]
    pkg = args.pkg or (base + "_pkg")
    array = args.array or (base + "_array")

    try:
        parse_memory_init(
            args.yaml_file,
            args.mem,
            args.sv,
            args.vhdl,
            pkg,
            array,
            enable_warnings=args.warning,
        )
    except Exception as e:
        print(f"Error occurred while parsing: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
