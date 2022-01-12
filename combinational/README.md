# Introduction

This directory provides a tutorial on how to create synthesizable behavior descriptions of combinational logic. All examples include testbenches for simulation, which uses the name of the module being simulated with a _tb.sv suffix. Testbenches are commented, but will be explained in detail in a different section of the tutorial.

# Methodology: design the circuit, then write the code.

As with all circuits, first design the combinational circuit, then write the code. With combinational logic, this methodology is often confusing because synthesis tools are generally very good at optimizing combinational logic. So, unlike other types of logic, you can write often combinational logic in many ways that will all synthesize to efficient circuits. However, you should at the very least consider the I/O interface before starting to write the code. You could also try to simplify the logic manually, but for pure combinational logic, synthesis tools will likely do a better job.

# Suggested Study Order

1. [2:1 mux](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational/mux2x1.sv)
    - Introduces basic constructs and guidelines for cobminational logic. 
    - Includes a top-level module mux2x1 that allows you to change the module that is synthesized.
    - Includes a testbench that tests all included modules at the same time.
1. [4-input Priority Encoder](https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/combinational/priority_encoder_4in.sv)
    - Introduces packed arrays.
    - Discusses appropriate situations for if and case statements.
1. [Parameterized Priority Encoder](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational/priority_encoder.sv)
    - Introduces parameters to support any number of inputs.
    - Introduces for loops inside always blocks.
    - Introduces local parameters.
    - Introduces how to convert an integer to any number of bits to avoid width mismatch problems.
1. [Adders](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational/add.sv)
    - Introduces arithmetic operations, blocking vs. non-blocking assignments, concatenation, automatic variable resizing.
    - Illustrates a variety of adders (no carry, carry out, carry in & out, carry in, out, and overlay)
1. [Multipliers](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational/mult.sv)
    - Introduces signed and unsigned, generate statements, and slicing.
    - Multiple testbenches to support the different multiplier interfaces.
    - A separate top-level module (mult_top.sv) for synthesizing the different modules.
1. [ALU](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational/alu.sv)
    - Introduces common problems with latches, strategies for avoiding latches, local parameters, and tasks.    

