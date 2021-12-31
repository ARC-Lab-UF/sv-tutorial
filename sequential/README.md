# Introduction

This directory provides a tutorial on how to create behavioral descriptions of sequential logic. Technically, sequential logic only includes flip-flops and registers
(possibly latches in rare case or for ASICs), so the tutorial actually shows of how to model circuits that are a combination of both sequential logic and
combinational logic. The ultimate purpose of this tutorial is to understand how registers get synthesized, and where the get placed in relation to other logic. One of the most
common mistakes when writing RTL is accidentally introducing an incorrect number of registers, in addition accidentally creating additional control logic that is unnecessary.

# Methodology: design the circuit, then write the code.

For circuits with sequential logic, designing the circuit means deciding exactly how many registers you want, and where those registers should be placed. Although synthesis 
optimizations may change this some (e.g. via retiming), use of registers is a critical design decision because it affects the timing of your design, which is something RTL 
synthesis cannot change. Similar to structural architectures, "designing the circuit" for sequential logic usually means creating a schematic that illustrates the exact number
and placement of all registers. With this schematic, you can easily apply the guidelines given below to ensure your design synthesizes as intended.

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
1. [Add Tree (TBD)]()
    - Introduces recursion.    
    

