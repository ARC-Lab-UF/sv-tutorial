# Introduction

This directory provides a tutorial on how to create finite state machines (FSMs) in SystemVerilog. The example demonstrates two different models, which I 
refer to as the 1-process/block and 2-process/block models. The 1-process model uses the coding guidelines from sequential logic to capture the state register,
next-state logic, and output logic in a single process. However, this model has the limitation of registering the outputs, which I don't recommend
unless you have a good reason to do so. The 2-process model uses one process for sequential logic (the state register) and another process for
combinational logic (next-state and output logic). I strongly recommend the 2-process model to avoid the extra cycle of delay on the output of the
1-process model.

You might see other people using 3- and 4-process models, but I've never seen an advantage. [This paper](http://www.sunburst-design.com/papers/CummingsSNUG2019SV_FSM1.pdf) is an excellent paper on different FSM coding styles. It reports advantages of their
3- and 4- process models, but I can represent everything in those models using 2 processes, so to my knowledge there is no inherent
technical advantage, possibly just a convenience advantage. In any case, I will explore the issue further and update the examples
for any new findings.

# Methodology: design the circuit, then write the code.

For FSMs, designing the circuit is a little more obvious, and corresponds to creating the states, transitions between states, and outputs for each
state and/or transition. Basically, you want create a diagram for the FSM. Given that diagram, it is trivial to convert the FSM into code, as shown
in the examples below.

# Suggested Study Order

1. [Moore](moore.sv)
    - Illustrates various architectures for a 1-process and 2-process model of a Moore state machine.
    - See the Moore diagram in [fsm.pdf](fsm.pdf) for an illustration of the FSM represented in code.
1. [Mealy](mealy.sv)
    - Illustrates various 2-process architectures for a Mealy state machine.
    - Illustrates a hybrid Moore/Mealy implementation.
    - See the Mealy and Hybrid Mealy diagram in [fsm.pdf](fsm.pdf) for an illustration of the FSMs represented in code.
    - NOTE: Provided testbench does not fully check for correctness.

    

