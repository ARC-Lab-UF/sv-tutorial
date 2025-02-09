// Greg Stitt
// University of Florida

// This file implements a basic AXI4 stream agent for the subset of the AXI4
// stream signals shown in axi4_stream_if.svh.
//
// The key point of this entire example is to recognize the potential reuse
// of this agent. Now that you have an AXI4 stream agent, you can use it for
// any DUT using AXI4 streaming, or across multiple interfaces instances of the
// same DUT. The latter is exactly what we are doing in this testbench. The 
// environment creates three instance--1 for each input, and 1 for the output--
// with the output using a different width.
//
// Once you have an agent for all of your DUT's interfaces, you solely have to
// change the DUT-specific classes, such as tests, environments, sequences, etc.

`ifndef _AXI4_STREAM_AGENT_SVH_
`define _AXI4_STREAM_AGENT_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_sequencer.svh"
`include "axi4_stream_driver.svh"
`include "axi4_stream_monitor.svh"

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
class axi4_stream_agent #(
    parameter int DATA_WIDTH = 32
) extends uvm_agent;
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_component_param_utils(axi4_stream_agent#(DATA_WIDTH))

    // Declare the parameterized sequencer, driver, and monitor.
    axi4_stream_sequencer #(DATA_WIDTH) sequencer;
    axi4_stream_driver #(DATA_WIDTH) driver;
    axi4_stream_monitor #(DATA_WIDTH) monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Instantiate the sequencer, driver, and monitor. Note the use of
        // parameters here.
        sequencer = axi4_stream_sequencer#(DATA_WIDTH)::type_id::create("sequencer", this);
        driver    = axi4_stream_driver#(DATA_WIDTH)::type_id::create("driver", this);
        monitor   = axi4_stream_monitor#(DATA_WIDTH)::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect the driver to the sequencer.
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
endclass

`endif
