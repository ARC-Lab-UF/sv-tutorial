// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_ITEM_SVH_
`define _AXI4_STREAM_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
class axi4_stream_seq_item #(
    parameter int DATA_WIDTH = 32
) extends uvm_sequence_item;
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_object_param_utils(axi4_stream_seq_item#(DATA_WIDTH))

    // Since we are only using a subset of the AXI4 stream signals, the 
    // transaction only needs the data being transferred.
    rand logic [DATA_WIDTH-1:0] data;

    function new(string name = "axi4_stream_seq_item");
        super.new(name);
    endfunction
endclass

`endif
