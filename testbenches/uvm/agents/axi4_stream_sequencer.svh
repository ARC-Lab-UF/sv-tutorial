// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_SEQUENCER_SVH_
`define _AXI4_STREAM_SEQUENCER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
//
// In addition, because uvm_sequencer has a parameter specifying the sequence
// item, we must provide axi4_stream_seq_item. However, since that seq item
// is now parameterized, we must also provide its parameter value.
class axi4_stream_sequencer #(
    parameter int DATA_WIDTH = 32
) extends uvm_sequencer #(axi4_stream_seq_item #(DATA_WIDTH));
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_component_param_utils(axi4_stream_sequencer#(DATA_WIDTH))

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif
