// Greg Stitt
// University of Florida

// This file implements a basic AXI4 stream agent for the interface 
// in axi4_stream_if.svh. We've now fully parameterized the agent to support
// different widths for the data and sideband signals.

`ifndef _AXI4_STREAM_AGENT_SVH_
`define _AXI4_STREAM_AGENT_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_sequencer.svh"
`include "axi4_stream_driver.svh"
`include "axi4_stream_monitor.svh"

// In this example, 
class axi4_stream_agent #(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) extends uvm_agent;
    // We have to provide all the parameters when registering the class.
    `uvm_component_param_utils(axi4_stream_agent#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    // Use all the parameters when declaring the sequencer, driver, and monitor.
    axi4_stream_sequencer #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) sequencer;
    axi4_stream_driver #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) driver;
    axi4_stream_monitor #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Instantiate the sequencer, driver, and monitor. Note the use of
        // parameters here.
        sequencer = axi4_stream_sequencer#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("sequencer", this);
        driver    = axi4_stream_driver#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("driver", this);
        monitor   = axi4_stream_monitor#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect the driver to the sequencer.
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
endclass

`endif
