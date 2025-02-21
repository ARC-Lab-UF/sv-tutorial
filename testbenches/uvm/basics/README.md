# Summary

This example provides a basic introduction to the Universal Verification Methodology (UVM). It builds on top of the earlier CRV
examples that introduces concepts such as monitors, drivers, etc. It is recommended you look over the simpler examples first if
you have no experience with UVM.

This testbench uses the most common features of UVM: uvm_config_db, interfaces, sequence items, monitors, driveres, sequencers,
agents, scoreboard, environments, sequences, and tests. Learning UVM is quite overwhelming at first, but once you internalize 
the purpose of each of these ideas, you'll quickly end up with a template that you can reuse with a few modifications across
many of your designs.

If you're thinking that UVM seems like overkill for a simple example, you are definitely right. I frequently do unit testing
using non-UVM testbenches. I generally use UVM when my module uses a standard interface (e.g., AXI) and has a non-trivial 
amount of functionality. For example, I wouldn't use it for an ALU, register, etc, but I might use it for a module that 
combines those things into a pipeline that streams inputs and outputs over AXI. When working with a large application,
I generally have UVM testbenches for the main components because it allows me to apply the same tests used for component-level
tests to top-level tests without any extra effort. This functionality will be shown in later examples. 

This initial example has some obvious limitations that we will address in later examples. First, it only has a single type of
test. Second, it only requires a single instance of an interface. This allows us to work around some annoyances related
to parameterized interfaces in UVM. Basically, we rely on the default width of the interface, which we set using a package
that can be accessed across all modules, interfaces, and classes. While not the most elegant approach, this strategy is
very convenient. However, it can only be used when all instances of an interface have the same parameter values, which although
common, will not always be the case.

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

1. [bit_diff_tb](bit_diff_tb.sv)    
    - Basic structure of UVM testbench.

1. [bit_diff_if](bit_diff_if.sv)    
    - The interface use by across all components.
    - Demonstrates default width assigned by package [bit_diff_if_pkg.sv](bit_diff_if_pkg.sv) as a workaround to avoid UVM headaches related to parameterized interfaces.

1. [bit_diff_item](bit_diff_item.svh)    
    - Introduces sequence items, which define the contents and abstraction level of the basic transactions used when testing the DUT.

1. [bit_diff_monitor](bit_diff_monitor.svh)    
    - Introduces UVM monitors and demonstrates two monitors that detect the beginning and end of the execution of the bit_diff module.

1. [bit_diff_driver](bit_diff_driver.svh)    
    - Introduces UVM drivers and demonstrates how to obtain a sequence item from a sequencer and drive the corresponding transaction onto the DUT.

1. [bit_diff_sequencer](bit_diff_sequencer.svh)    
    - Introduces UVM sequencers.

1. [bit_diff_agent](bit_diff_agent.svh)    
    - Introduces UVM agents, which combine monitors, drivers, and sequencers to provide reusable functionality for a specific interface.

1. [bit_diff_scoreboard](bit_diff_scoreboard.svh)    
    - Introduces UVM scoreboards, which track failed tests and various statistics.

1. [bit_diff_env](bit_diff_env.svh)    
    - Introduces UVM environments, which connect the agent's monitors to the scoreboard for this example.

1. [bit_diff_sequence](bit_diff_sequence.svh)    
    - Introduces UVM sequences, which provide stimilus generation via a stream of sequence_items.

1. [bit_diff_base_test](bit_diff_base_test.svh)    
    - Introduces UVM tests, which are the top-level of the hierachy. This file provides an abstract base class that provides functionality for other actual tests.

1. [bit_diff_simple_test](bit_diff_simple_test.svh)    
    - Our actual test for this example, which uses a single bit_diff_sequence consisting of bit_diff_items, to test the functionality of the DUT.