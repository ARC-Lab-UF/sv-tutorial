`ifndef _AXI4_STREAM_ITEM_SVH_
`define _AXI4_STREAM_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class axi4_stream_seq_item #(
    parameter int DATA_WIDTH = 32
) extends uvm_sequence_item;
    `uvm_object_param_utils(axi4_stream_seq_item#(DATA_WIDTH))

    rand logic [DATA_WIDTH-1:0] data;

    function new(string name = "axi4_stream_seq_item");
        super.new(name);
    endfunction
endclass

`endif
