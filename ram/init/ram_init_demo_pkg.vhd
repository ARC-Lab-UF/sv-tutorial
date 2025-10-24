library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package ram_init_demo_pkg is

    constant C_NUM_ELEMENTS  : integer := 64;
    constant C_ELEMENT_WIDTH : integer := 8;
    constant C_TOTAL_BITS    : integer := C_NUM_ELEMENTS*C_ELEMENT_WIDTH;
    type ram_init_demo_array_t is array(0 to C_NUM_ELEMENTS-1) of std_logic_vector(C_ELEMENT_WIDTH-1 downto 0);

    -- Automatically generated constant array
    constant RAM_INIT_DEMO_ARRAY : ram_init_demo_array_t :=
    (
        0 to 7 => x"FF",
        8 => x"10",
        9 => x"12",
        10 => x"14",
        11 => x"16",
        12 => x"18",
        13 => x"1A",
        14 => x"1C",
        15 => x"1E",
        16 => x"AA",
        17 => x"55",
        18 => x"77",
        19 => x"AA",
        20 => x"55",
        21 => x"77",
        22 => x"AA",
        23 => x"55",
        24 => x"1D",
        25 => x"10",
        26 => x"19",
        27 => x"1B",
        28 => x"16",
        29 => x"18",
        30 => x"1D",
        31 => x"15",
        32 => x"BC",
        33 => x"A0",
        34 => x"55",
        35 to 63 => x"00"
    );

    -- Convert array to SLV (for VHDL-93)
    function to_slv(a : ram_init_demo_array_t) return std_logic_vector;

    constant RAM_INIT_DEMO_ARRAY_SLV : std_logic_vector(C_TOTAL_BITS-1 downto 0) := to_slv(RAM_INIT_DEMO_ARRAY);

end package ram_init_demo_pkg;

package body ram_init_demo_pkg is

    function to_slv(a : ram_init_demo_array_t) return std_logic_vector is
        variable result : std_logic_vector(C_TOTAL_BITS-1 downto 0);
    begin
        for i in a'range loop
            result((i+1)*C_ELEMENT_WIDTH-1 downto i*C_ELEMENT_WIDTH) := a(i);
        end loop;
        return result;
    end function;

end package body ram_init_demo_pkg;
