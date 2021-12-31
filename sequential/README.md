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

1. [Register](register.sv)
    - Illustrates how to create an asynchronous reset, a synchronous reset, an enable/load, and a highly parameterized register with different reset types and activiation levels.
1. [Examples of Synthesizing Behavioral Code to a Specific Structure](seq_example.sv)
    - See [architectures.pdf](architectures.pdf) for different example circuits. Each one has a corresponding module in [seq_example.sv](seq_example.sv).
    - Illustrates common mistakes with sequential logic.
    - Goes over the use of non-blocking assignments and blocking assignments to accomplish different goals.
    - Suggestion: synthesize each module and use an RTL viewer to ensure the schematic matches the architecture in the pdf.
1. [Delay (TBD)]()
    

