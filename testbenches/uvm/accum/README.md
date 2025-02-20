# Summary

This example extends the previous examples by 1) demonstrating how to simulate using transactions at different 
abstraction levels, 2) how to use multiple tests, 3) how to define more complex constraints, and 4) how to
create parameterized covergroups.

The DUT for this example is an AXI4 stream accumulator. It accumulates packets of inputs, where the end of each
packet is specified by the assert of AXI's tlast signal on the input. The DUT generates an output for each valid
input, but also signifies the end of each packet by asserting tlast on the output interface.

The new testbench provides a test that simulates individual inputs, and a separate test that simulates individual
packets. Packets have the advantage of a higher abstraction level, which could be more convenient for complex
simulations. Individual beats have the advantage of improved visibility. For example, when an error occurs,
the testbench will report the error in the cycle that it occurs. With packet-level simulations, error checking
is only done after receiving an entire packet, so if an error occurs, you only know that it occurred somewhere
after the last packet was checked.

# Simulation instructions

There are now two tests, so we need a way to specify which test we want using the makefile. We could just edit
the makefile to change the UVM_TESTNAME variable, but that is pretty tedious. Instead, we can specify the
testname on the command line like this:

`make UVM_TESTNAME=accum_packet_test sim`
`make UVM_TESTNAME=accum_single_beat_test sim`

Or, you can rely on the default specified in the Makefile:

`make sim`

# Suggested Study Order

I strongly suggest reading the files in the following order, due to the comments assuming this ordering when explaining topics.
Make sure you have already studied the previous example to ensure you understand the basics of agents. Note that many of the
files have not changed. Files that are not listed are identical or similar to the previous example and have only been updated
for the new DUT.

1. [axi4_stream_seq_item](axi4_stream_seq_item.svh)    
    - Updated sequence item to support transactions at different abstraction levels.
    - Demonstrates dynamic arrays.

1. [axi4_stream_monitor](axi4_stream_monitor.svh)    
    - Updated to monitor individual beats, or to gather entire packets before sending transaction through an analysis port.

1. [axi4_stream_driver](axi4_stream_driver.svh)    
    - Extended to drive but individual beats or entire packets.

1. [axi4_stream_agent](axi4_stream_agent.svh)    
    - Minor modifications to help configure the abstraction level of the transactions.

1. [accum_scoreboard](mult_scoreboard.svh)    
    - Modified to compare expected and actual results for both individual beats and entire packets.

1. [Coverage Classes](mult_coverage.svh)    
    - Extended to show parameterization of complex cover groups.

1. [Sequences](accum_sequence.svh)    
    - Provides a base sequence with common functionality, along with a sequence for individual beats, and another sequence for entire packets.
    - Demonstrates more advanced constraints to help concisely randomize the AXI interfaces for beats and packets.

1. [accum_env](accum_env.svh)    
    - Minimal changes to configure the transaction abstraction level in each agent.

1. [accum_single_beat_test](accum_single_beat_test.svh)    
    - Defines a test for the accumulator that uses single-beat transactions.

1. [accum_packet_test](accum_packet_test.svh)    
    - Defines a test for the accumulator that uses packet transactions.