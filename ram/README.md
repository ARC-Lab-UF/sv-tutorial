# Summary

This directory contains a number of simple dual-port (SDP) and true dual-port (TDP) inference templates
that work on most FPGAs from Xilinx/AMD and Intel/Altera.

Note that the code as provided will only work in Quartus Prime Pro. You can extend it to
work in other Quartus versions, but those versions don't have great support for SystemVerilog,
and I didn't want to write all the code for the tool with the weakest support.

# Suggested Study Order

1. [ram_sdp](ram_sdp.sv)    
    - Illustrates a variety of single dual-port inference templates with different features.
    - Demonstrates a generalized, configurable template that combines these features.
    - Includes Vivado and Quartus-specialized templates.
    - Includes a [testbench](ram_sdp_tb.sv) for the generalized template.

1. [ram_sdp_with_reset](ram_sdp_with_reset.sv)    
    - Illustrates how to modify the general template with a reset for some of the optional registers.
    - Explains the risks of using resets improperly in RAM templates.

1. [ram_tdp](ram_tdp.sv)    
    - Explains a generalized true dual-port RAM inference template.
    - Supports both Vivado and Quartus Prime Pro.
    - Requires corresponding TDP memories in targetted FPGA.
