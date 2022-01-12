# Introduction

This repository provides a tutorial on how to write synthesizable SystemVerilog code. It touches on verification topics, but the primary focus is on code for synthesis. Most of the provided examples include multiple implementations that illustrate common mistakes, different ways of implementing the same circuit, or different tradeoffs.

# Prerequisites

This tutorial assumes you already have a background in digital logic, synthesis tools, and simulators. All examples have been tested in Quartus and Modelsim, for which there are free versions available for students.

# Methodology: design the circuit, then write the code.

My biggest suggestion for writing synthesizable code in any language is to design the circuit, then write the code. Basically, you should be able to hierarchically divide a large circuit into smaller and smaller components, until each component is either combinational logic, sequential logic, a combination of both (e.g., a datapath), finite state machines, or memories. Then, you can simply follow the following synthesis guidelines for each of these types of circuits. Note that some of the guidelines contradict each other if used for the wrong type of logic, which is why it is always important to know the type of logic that you are designing. In other words, don't start writing the code until you know what type of circuit you are describing. If you are creating a structural archiecture, draw the schematic first. If you are designing a state machine, draw the FSM first. If you are designing a circuit with registers, first figure out exactly where you want registers, etc.

# Suggested Study Order

1. [Combinational Logic](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/combinational)
1. [Structural Architectures](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/structural)
1. [Sequential Logic](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/sequential)
1. [Finite-State Machines](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/fsm)
1. [Finite-State Machines + Datapaths](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/fsmd)
1. [Problematic Coding Practices (Gotchas)](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/gotchas)
1. [Testbenches](https://github.com/ARC-Lab-UF/sv-tutorial/tree/main/testbenches)
