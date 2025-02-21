// Greg Stitt
// University of Florida

// This file is unchanged from the previous example.

`ifndef _AXI4_STREAM_SEQUENCER_SVH_
`define _AXI4_STREAM_SEQUENCER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class axi4_stream_sequencer #(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) extends uvm_sequencer #(axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH));
    // We need to provide all parameters when registering the class.
    `uvm_component_param_utils(axi4_stream_sequencer#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif
