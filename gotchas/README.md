# Introduction

This directory looks at some of the common SystemVerilog "gotchas." These gotchas are potentially problematic constructs or practices that often lead to bugs that are difficult 
to identify. One challenge with SystemVerilog is that it does much more for you automatically than VHDL. Unfortunately, these automatic changes often disguise design mistakes that
may not even result in warnings. As much as possible, our goal is to catch problems at compile time because debugging in simulation is much harder. In some situations, these
gotchas can result in differences between simulation and synthesized behavior, which requires debugging on an FPGA. Such debugging is incredibly difficult and should be avoided
whenever possible. To avoid these situations, it is very important to avoid these gotchas.

# Suggested Study Order

1. [mult_add](mult_add.sv)
    - Gotchas: automatic net inference and automatic width conversion
1. [4:1 mux](mux4x1.sv)
    - Gotcha: invalid array indexes in unpacked arrays.
    - Make sure to look at both the [module](mux4x1.sv) and [testbench](mux4x1_tb.sv) since the testbench has its own gotchas.    
1. [ram](ram.sv)
    - Gotcha: index truncation in unpacked arrays.
    - Note: there is no testbench for this example. The intent is to synthesize it and see that there are no errors are warnings, despite an obvious problem in the code.
1. [structure](structure.sv)
    - Gotcha: width mismatches in structural architectures.
