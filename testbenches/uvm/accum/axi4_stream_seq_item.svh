// Greg Stitt
// University of Florida

// In this example, we fully parameterize the sequence item to handle different 
// width for the data and sideband signals.

`ifndef _AXI4_STREAM_ITEM_SVH_
`define _AXI4_STREAM_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class axi4_stream_seq_item #(
    parameter int DATA_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter int DEST_WIDTH = 4,
    parameter int USER_WIDTH = 4
) extends uvm_sequence_item;
    `uvm_object_param_utils(axi4_stream_seq_item#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    // In this example, we add a bit to specify in the sequence item captures a
    // transaction that is an entire packet, or an individual beat of a packet.
    bit is_packet_level;
    
    rand logic [DATA_WIDTH-1:0] tdata[];
    rand logic [DATA_WIDTH/8-1:0] tstrb[];
    rand logic [DATA_WIDTH/8-1:0] tkeep[];
    logic tlast = 1'b0;
    logic [ID_WIDTH-1:0] tid = '0;
    logic [DEST_WIDTH-1:0] tdest = '0;
    logic [USER_WIDTH-1:0] tuser = '0;

    function new(string name = "axi4_stream_seq_item");
        super.new(name);
        // By default, we'll use individual beats.
        is_packet_level = 1'b0;
        tdata = new [1];
        tstrb = new [1];
        tkeep = new [1];
        tstrb[0] = '1;
        tkeep[0] = '1;
    endfunction

    function automatic void init_from_queue(axi4_stream_seq_item#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) q[$]);
        if (q.size() == 0) return;
    
        tdata = new [q.size()];
        tstrb = new [q.size()];
        tkeep = new [q.size()];
        
        foreach(q[i]) begin
            tdata[i] = q[i].tdata[0];
            tstrb[i] = q[i].tstrb[0];
            tkeep[i] = q[i].tkeep[0];
        end

        tid = q[0].tid;
        tdest = q[0].tid;
        tuser = q[0].tid;

        is_packet_level = 1'b1;
    endfunction
endclass

`endif
