// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_ITEM_SVH_
`define _AXI4_STREAM_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
class axi4_stream_seq_item #(
    parameter int DATA_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter int DEST_WIDTH = 4,
    parameter int USER_WIDTH = 1
) extends uvm_sequence_item;
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_object_param_utils(axi4_stream_seq_item#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    rand logic [DATA_WIDTH-1:0] tdata;

    logic [DATA_WIDTH/8-1:0] tstrb = '1;
    logic [DATA_WIDTH/8-1:0] tkeep = '1;
    logic tlast = 1'b0;
    logic [ID_WIDTH-1:0] tid = '0;
    logic [DEST_WIDTH-1:0] tdest = '0;
    logic [USER_WIDTH-1:0] tuser = '0;

    function new(string name = "axi4_stream_seq_item");
        super.new(name);
    endfunction
endclass

`endif
