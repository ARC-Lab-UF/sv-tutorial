# Introduction

This tutorial provides a basic introduction to testbenches and verification using various constructs in SystemVerilog. This is not intended to be a comprehensive tutorial, but 
provides a good starting point. The Universal Verification Methodology (UVM) is recommended for advanced testing.

# Overview

To test a design, we need a module to drive the inputs so we can verify the functionality. That module is usually referred to as a testbench. In its most simple form, a 
testbench simply applies a set of inputs, waits some amount of time for the outputs to change, then applies new inputs. In a slightly more advanced form, the testbench also
verifies that outputs are correct. In more advanced forms, the testbench should check to ensure that certain properties are always true, while also checking for different 
types of coverage (e.g., was every statement tested, were all relevant values tested, were all transitions tested, etc.). There are many strategies ranging from simple ad-hoc
testbench strategies, to more advanced and more formal strategies such as UVM.

# Suggested Study Order

## Basic testbench constructs

Here are examples of non-ideal, but easy to understand testbenches that introduce basic constructs. We will later improve upon all these examples.

1. [2:1 Mux](basic/mux2x1_tb.sv)
    - Corresponding [module](basic/mux2x1.sv) and [testbench](basic/mux2x1_tb.sv).
    - Basic introduction into testbenches. Introduces timescale, waiting, functions, $timeformat, and $display.

1. [Race Condition Intro](basic/race.sv)
    - Demonstration of common race condition problems, and how to avoid them.
    - Introduces $stop, $finish. 

1. [Reset Race Conditions](basic/reset_race.sv)
    - Demonstration of reset race conditions, and how to avoid them.
    - Introduces clock generation, waiting for rising edges, disable. 

1. [Race Conditions: the Root of All Verilog Evil](https://stitt-hub.com/race-conditions-the-root-of-all-verilog-evil/)
    - Demonstration of other common race conditions.
    - Low-level analysis of different simulation orders causing race conditions. 

1. [Register](basic/register_tb.sv)
    - Corresponding [module](basic/register.sv) and [testbench](basic/register_tb.sv).
    - Introduces $urandom and special cases for disable. 
    - Demonstrates a commonly used problematic testbench strategy.
    
## Assertions

In the basic testbench examples above, we manually check for errors with if statements combined with error messages. Although useful for simple tests, assertions are a much 
more powerful construct that can be used to verify that any condition is true at any point in time. Most importantly, assertions can be combined with properties and sequences
to verify complex behaviors concisely. We will see situations where many lines of testbench code can be replaced by a single assertion.

1. [2:1 Mux (extends earlier example with immediate assertion)](assertions/mux2x1_tb.sv)
    - Corresponding [module](assertions/mux2x1.sv) and [testbench](assertions/mux2x1_tb.sv).
    - Shows basic syntax for immediate assertions.    
1. [Flip-flop](assertions/ff_tb.sv)
    - Corresponding [module](assertions/ff.sv) and [testbench](assertions/ff_tb.sv).
    - Introduces concurrent assertions, properties, sequences, and implication.
    - Introduces $past and $stable.
1. [Register](assertions/register_tb.sv)
    - Corresponding [module](assertions/register.sv) and [testbench](assertions/register_tb.sv).
    - Demonstrates subtle problems that can cause assertion failures.
    - Demonstrates how to disable assertions.
    - Expands on implication and illustrates a significant improvement to the basic register testbench that lacked assertions.    
1. [Delay](assertions/delay.sv)
    - Corresponding [module](assertions/delay.sv) and [testbench](assertions/delay_tb.sv).
    - Introduces queues.
    - Expands on $past. 
    - Expands on implication and sequences.
    - Demonstrates go-to replication and throughout operators.
1. [Simple Pipeline w/ Enable](assertions/simple_pipeline_with_en.sv)
    - Corresponding [module](assertions/simple_pipeline_with_en.sv) and [testbench](assertions/simple_pipeline_with_en_tb.sv).
    - Introduces common problem with calling functions in assertions.
    - Introduces highly reusable template for pipeline testbenches.    
1. [FIFO](assertions/fifo.sv)
    - Corresponding [module](assertions/fifo.sv) and [testbench](assertions/fifo_tb.sv).
    - Introduces hierarchical access of variables inside other modules.
    - Demonstrates incorrect and correct ways to preserve ordering of data in assertion properties.
    - Demonstrates simple queue model as an alternative to complex assertions.
    - Demonstrates assertions within the [synthesizable code.](assertions/fifo.sv)

## Coverage

Whereas assertions are generally used to check for correct functionality, coverage constructs are used to ensure that desired tests actually occurred. For example, if we only
test 3 input combinations for a module and all the assertions pass, although we haven't found any problems, we have done very little to verify the design.
While there are many types of coverage, we will look at ways of sampling events and values to ensure that all desired tests have actually occurred. With the combination of 
high coverage and no failed assertions, we gain much more confidence in the correct functionality of a design.

1. [FIFO](coverage/fifo_tb.sv)
    - Corresponding [module](coverage/fifo.sv) and [testbench](coverage/fifo_tb.sv).
    - Introduces cover properties.
1. [Add](coverage/add_tb.sv)
    - Corresponding [module](coverage/add.sv) and [testbench](coverage/add_tb.sv).
    - Extends cover properties and introduces cover groups and cover points.
1. [FSM (TBD)]()

## Constrained-Random Verification (CRV)

1. [Add](crv/add_tb.sv)
    - Corresponding [module](crv/add.sv) and [testbench](crv/add_tb.sv).
    - Introduces classes, rand, randc, randomize(), custom distributions.

2. [Bit Diff FSMD (VERY IMPORTANT)](crv/bit_diff_tb.sv)
    - Corresponding [module](crv/bit_diff.sv) and [testbench](crv/bit_diff_tb.sv).
    - Introduces generators/sequences, drivers, monitors, scoreboards, environments, tests, interfaces, BFMs, mailboxes, join.
    - Teaches basic concepts needed to understand UVM principles.

2. [Bit Diff FSMD Object-Oriented TB](crv/bit_diff_oop)
    - Cleaned up version of previous example
    - Demonstrates base classes and inheritance using different generators, drivers, monitors, and tests.

## UVM
    
1. TBD
