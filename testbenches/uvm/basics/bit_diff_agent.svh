// Greg Stitt
// University of Florida

// A UVM agent is essentially what most people would refer to as a BFM. It
// combines monitors and drivers for a specific interface. While the advantages
// of an agent might not seem obvious for an application-specific interface,
// they become more clear when applied to a more general interface like AXI. 
// For something like AXI, once you have an AXI agent, you can reuse it to get
// get monitoring and driving capabilities for any DUT that uses AXI. You might
// also have a DUT with multiple AXI interfaces, for which you could just 
// instantiate multiple agents. Essentially, the advantage of an agent is the
// ability to reuse an interface's monitors and drivers.

`ifndef _BIT_DIFF_AGENT_SVH_
`define _BIT_DIFF_AGENT_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"
`include "bit_diff_sequencer.svh"
`include "bit_diff_sequence.svh"
`include "bit_diff_driver.svh"
`include "bit_diff_monitor.svh"

class bit_diff_agent extends uvm_agent;
    `uvm_component_utils(bit_diff_agent)

    // A UVM agent provides drivers, monitors, and a sequencer that will enable
    // a test to send sequences to the driver.
    bit_diff_driver driver;
    bit_diff_sequencer sequencer;
    bit_diff_start_monitor start_monitor;
    bit_diff_done_monitor done_monitor; 

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Use the factory to create instances of the monitors, driver, and sequencer.
        start_monitor = bit_diff_start_monitor::type_id::create("start_monitor", this);
        done_monitor = bit_diff_done_monitor::type_id::create("done_monitor", this);
        driver = bit_diff_driver::type_id::create("driver", this);
        sequencer = bit_diff_sequencer::type_id::create("sequencer", this);
    endfunction

    // Connect the driver to the sequencer.
    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction

endclass

`endif
