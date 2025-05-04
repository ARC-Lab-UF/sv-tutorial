# Summary

This directory contains a number of simple dual-port (SDP) and true dual-port (TDP) inference templates
that work about most FPGAs from Xilinx/AMD and Intel/Altera.

Note that the code as provided will only work in Quartus Prime Pro. You can extend it to
work in other Quartus versions, but those versions don't have great support for SystemVerilog,
and I didn't want to write all the code for the tool with the weakest support.

# Suggested Study Order


1. [ram_sdp](ram_sdp.sv)    
    - Illustrates a variety of single dual-port inference templates with different features.
    - Demonstrates a generalized, configurable template that combines these features.
    - Includes Vivado and Quartus-specialized templates.
    - Includes a [testbench](ram_sdp_tb.sv) for the generalized template.

1. [ram_sdp_with_reset_vivado](ram_sdp_with_reset_vivado.sv)    
    - Illustrates how to modify the Vivado template with reset for some of the optional registers.
    - Explains the risks of using resets improperly in RAM templates.

1. [ram_tdp](ram_tdp.sv)    
    - Explains a generalize true dual-port RAM inference template.

1. [ram_tdp_quartus](ram_tdp_quartus.sv)    
    - Demonstrates how to specialize the TDP template for Quartus Prime Pro and Intel/Altera FPGAs.

1. [ram_tdp_vivado](ram_tdp_vivado.sv)    
    - Demonstrates how to specialize the TDP template for Vivado and AMD/Xilinx FPGAs.