# Introduction

This directory provides a tutorial on how to create structural descriptions, which are generally just code representations of a schematic. A schematic is just an interconnection
of existing components, which can be any type of logic, and any level of granularity.

# Methodology: design the circuit, then write the code.

For structural descriptions, designing the circuit means creating the schematic. For every component in the schematic, you will simply instantiate an existing module 
(or create one if necessary), and then connect them together as shown in the schematic. The primary creativity in structural descriptions is identifying patterns (or exceptions) 
in the structure that can be described with generate constructs, as the examples will show.

# Suggested Study Order

1. [4:1 mux](mux4x1.sv)
    - Illustrates the basic techniques for converting a schematic (in this case [mux4x1.pdf](mux4x1.pdf)) into SystemVerilog code.    
1. [Ripple-Carry Adder](ripple_carry_adder.sv)
    - Introduces parameters and the for-generate construct.    
    - See the schematic [ripple_carry_adder.pdf](ripple_carry_adder.pdf) for reference.
    - ***Important point:*** Use the "for generate" statement anytime that there is a pattern in a structural description. This construct will allow you to specify very large structures with very little code.
1. [Delay](delay.sv)
    - Introduces unpacked arrays, if generate, and parameter validation techniques.    
    - See the schematic [delay.pdf](delay.pdf) for reference.
1. Recursive Architectures (advanced)
    - [Adder Tree Explanation](https://stitt-hub.com/you-can-and-should-write-recursive-rtl-code/)    
    - [Optimized Adder Tree](https://stitt-hub.com/you-can-and-should-write-recursive-rtl-part-2/)
