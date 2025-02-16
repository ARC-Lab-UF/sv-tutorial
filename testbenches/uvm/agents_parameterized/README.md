# Summary

This example extends the previous example by completely parameterizing the AXI4 stream interface with parameters that
control the width of the data and all of the optional sideband signals.

The code illustrates how to handle multiple parameters when instantiating and registering classes. It also demonstates
the use of a package to define default parameter widths to simplify classes by only requiring specification of the
parameters that change for the given application.

The end result is a highly reusable, highly flexible AXI4 stream agent that can support any number of interfaces,
with each interface having different widths for data and sideband signals, if desired.

Note that despite changing the interface, agent, and sequence items, the only application-specific modules that
had to change were the scoreboard and coverage classes, which both required the new sequence item.

The DUT is the same streaming multiplier from the previous example.

# Suggested Study Order

I strongly suggest reading the files in the following order, due to the comments assuming this ordering when explaining topics.
Make sure you have already student the previous example to ensure you understand the basics of agents. Note that many of the
file have not changed. Files that are not listed are identical to the previous example.


1. [axi4_stream_pkg](axi4_stream_pkg.sv)    
    - Package that defines the default values of all AXI4 stream parameteres.
    - These may be modified to universally change the defaults across all agents.

1. [axi4_stream_if](axi4_stream_if.svh)    
    - Illustrates a complete AXI4 stream interface with parameters to control width of data and sideband signals.
    - Uses default parameter values from axi4_stream_pkg.

1. [axi4_stream_seq_item](axi4_stream_seq_item.svh)    
    - Updated sequence item that contains both the AXI4 stream data and sideband signals.
    - Supports all parameters of the AXI4 stream interface.

1. [axi4_stream_monitor](axi4_stream_monitor.svh)    
    - Extends previous version with complete parameterization.
    - Illustrates how to instantiate classes requiring multiple parameters.
    - Extended to transfer data and sideband information via analysis port.

1. [axi4_stream_driver](axi4_stream_driver.svh)    
    - Extended previous version to support complete parameterization.

1. [axi4_sequencer](axi4_sequencer.svh)    
    - Extended previous version to support complete parameterization.

1. [axi4_stream_agent](axi4_stream_agent.svh)    
    - Extended previous version to support complete parameterization.
    - Demonstrates how to instantiate the paramterized driver, monitor, and sequencer.    

1. [mult_scoreboard](mult_scoreboard.svh)    
    - Modified to support the new parameterized sequence item.
    - Leverages default interface parameters to avoid having to define values of all parameters.

1. [Coverage Classes](mult_coverage.svh)    
    - Extended to support parameterized sequence item.
    - Demonstrates how to leverage typedefs to create concise code when working with parameterized types.

1. [mult_env](mult_env.svh)    
    - Despite the paramterized interface, this environment is identical to the previous one due to the leveraging of default interface values.
    - Demonstrates how to instantiate agents, interfaces, etc. with multiple parameters when you can't rely on default values.

