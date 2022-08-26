# Introduction

This directory provides a tutorial on how to create controllers and datapaths to implement a specific algorithm. The examples demonstrate two different specification styles: 
FSMDs and FSM+Ds. An FSMD describes both the controller and datapath functionality at the same time in a single module. An FSM+D first creates an explicit datapath and a 
corresponding controller, and then combines them together. 

# Methodology: design the circuit, then write the code.

For FSMDs and FSM+Ds, designing the circuit first requires designing an algorithm, which in many cases of hardware design is provided by a separate designer. For an FSMD,
the next step in designing the circuit is breaking up the operations in the algorithm into separate states. The resulting design is essentially a finite state machine, but
where instead of just having outputs and next-state transitions, you also have datapath operations assigned to states. After creating a diagram for this FSMD, there is a
straightfoward translation into code. For FSM+Ds, the next step after creating the algorithm is to design a datapath to provide the necessary resources. You then create a 
module to capture this datapath, often structurally using other modules. After designing the datapath, you then create a corresponding controller, which is just a normal
FSM. In some cases, that FSM will match the control states of the FSMD, but not always. After designing the controller, the FSM+D simply connects the controller with the
datapath to provide a complete solution.

# Suggested Study Order

1. [Bit Difference Calculator](bit_diff.sv)
    - Introduces 1- and 2-process FSMDs.
    - Introduces FSM+Ds with 3 different datapaths.
    - See the included bit_diff.pdf for an illustration of the FSMD and different datapaths.
    - Includes a top-level module bit_diff that allows you to change the module that is synthesized.
