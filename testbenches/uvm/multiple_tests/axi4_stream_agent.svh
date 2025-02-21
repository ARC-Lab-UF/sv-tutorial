// Greg Stitt
// University of Florida

// This file is nearly identical to the previous example. It simply adds the
// configure_transaction_level function to configure the driver and monitor.

`ifndef _AXI4_STREAM_AGENT_SVH_
`define _AXI4_STREAM_AGENT_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class axi4_stream_agent #(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) extends uvm_agent;
    `uvm_component_param_utils(axi4_stream_agent#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    axi4_stream_sequencer #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) sequencer;
    axi4_stream_driver #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) driver;
    axi4_stream_monitor #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Helper function to configure the transaction level of the driver and
    // monitor.
    function automatic void configure_transaction_level(bit is_packet_level);
        driver.is_packet_level = is_packet_level;
        monitor.is_packet_level = is_packet_level;        
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        sequencer = axi4_stream_sequencer#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("sequencer", this);
        driver    = axi4_stream_driver#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("driver", this);
        monitor   = axi4_stream_monitor#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
endclass

`endif
