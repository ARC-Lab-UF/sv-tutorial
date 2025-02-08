`ifndef _AXI4_STREAM_SEQUENCER_SVH_
`define _AXI4_STREAM_SEQUENCER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

class axi4_stream_sequencer extends uvm_sequencer #(axi4_stream_seq_item);
    `uvm_component_utils(axi4_stream_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif