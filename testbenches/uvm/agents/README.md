# Summary

This example extends the previous example by demonstrating more advanced UVM concepts. The main new concepts that are explained
include how to handle parameterized interfaces, how to create reusable agents for standard interfaces, how to use multiple
interface instances with different widths, and how to use analysis ports. It also demonstrates how to integrate converage classes
with UVM.

Perhaps the most significant takeaway point of this example is the significant code reuse enabled by UVM agents. This
example uses an AXI4-streaming multiplier that has two streaming interfaces providing inputs, and another interface
(of a different width) providing outputs. Unlike the previous example, where we created an application-specific interface
and then created monitors, drivers, and agents for that interface, in this example we use a standard interface (AXI4 stream).
The key point of UVM agents is that they are intended to handle all the driving and monitoring for a specific interface. So,
if you already have an AXI4 stream agent, you do not need any new drivers or monitors. You simply instantiate a separate
agent for each AXI4 instance (2 inputs and 1 output), and configure them according to the DUT's requirements.

By reusing agents for common interfaces, updating a UVM testbench only requires changes to the application-specific parts:
tests, environments, sequences, scoreboards, etc. You simply provide agents with transcations to drive, and receive data
from the agent's monitors.

Regarding the DUT, the use of an AXI4 streaming multplier is somewhat synthetic. To keep the latency at one cycle, the implementation
uses practices I would normally consider to be unsafe for AXI modules. However, I wanted as simple of a DUT as possible to avoid overwhelming the
reader. Ultimately, I wanted the simplest DUT that would demonstrate the main points of UVM that are explained in this example, as opposed to
demonstrating how to most effectively create an AXI streaming multiplier.

# Simulation instructions

This example include a makefile that will run if you have Questa installed and
all the corresponding environment variables loaded.

To compile without running a simulation:

`make`

To compile and run a command-line simulation:

`make sim`

To compile and open the GUI to run a simulation interactively:

`make gui`

# Suggested Study Order

I strongly suggest reading the files in the following order, due to the comments assuming this ordering when explaining topics.

1. [mult](mult.sv)    
    - Demonstrates an AXI4-stream multiplier that we will use as our DUT.

1. [mult_tb](mult_tb.sv)    
    - Demonstrates the use of three separate AXI4 stream interfaces.

1. [axi4_stream_if](axi4_stream_if.sv)    
    - Illustrates an AXI4 stream interface. The optional signals have been removed for now to keep the testbench simple, but they will be
    added in a later example.
    - Note that in most cases, you would not need to create this interface. Since it is a standard interface, there would likely be open implementations.

1. [axi4_stream_seq_item](axi4_stream_seq_item.svh)    
    - Defines the AXI4 stream sequence item.
    - For this example, the sequence item is simply the data provided over AXI.
    - When implementing the entire AXI4 stream protocol, this seq item might also include other optionsal flags that are part of the complete AXI4 stream interface,

1. [axi4_stream_monitor](axi4_stream_monitor.svh)    
    - Implements the AXI4 stream monitor. Note that this monitor is completely independent of the DUT and can be reused by any AXI stream interface.
    - Demonstrates usage of uvm_analysis ports, where after the monitor detects a relevant transaction, it sends to the corresponding data to
    the analysis port, where it can be read by multiple consumers.
    - Note that the actual destinations of the analysis port are not defined here. This is intentional since the agent is supposed to be independent
    of the DUT. We want the connections to be made somewhere specific to the DUT, which is usually the environment.

1. [axi4_stream_driver](axi4_stream_driver.svh)    
    - Implements the AXI4 stream driver. Note that this driver is completely independent of the DUT and can be reused by any AXI stream interface.

1. [axi4_sequencer](axi4_sequencer.svh)    
    - Implements the AXI4 stream sequencer.

1. [axi4_stream_agent](axi4_stream_agent.svh)    
    - Demonstrates a reusable AXI4 stream agent that combines a monitor, driver, and sequencer to handle all AXI transactions.
    - Note that after creating this agent, it can be reused for any DUT that uses AXI, or across multiple instances of the same DUT.

1. [mult_scoreboard](mult_scoreboard.svh)    
    - Simple scoreboard for the multiplier.
    - Demonstrates analysis exports, which are sinks for any analysis ports.
    - Demonstrates analysis FIFOs, which simplify synchronization between analysis ports and exports.

1. [Coverage Classes](mult_coverage.svh)    
    - Demonstrates how to integrate coverage with UVM.
    - Defines several classes, covergroups, and coverpoints.    

1. [mult_env](mult_env.svh)    
    - Instantiates the three agents: one for each AXI interface on the DUT.
    - Establishes all the connections between the analysis ports and exports.
    - Connects the three DUT interfaces to the corresponding agents.
    - Configures the drivers with specific timing options to improve testing.
    - Connects the agents' monitors to the corresponding coverage classes.

1. [mult_sequence](mult_sequence.svh)    
    - Provides some simple stimimulus generation that consists of a random sequence of input values.
    - Since the DUT uses two separate interfaces for the multiplier inputs, we'll use a separate sequence for each.

1. [mult_base_test](mult_base_test.svh)    
    - Provides basic, common functionality needed by any test.

1. [mult_simple_test](mult_simple_test.svh)    
    - Actual test for the multiplier.
    - Simply instatiates two mult_sequences, one for each input, and then sends the to the agent's drivers via the sequencers.
    - Demonstrates use of a fork two send two sequence at the same time, as opposed to one after the other.