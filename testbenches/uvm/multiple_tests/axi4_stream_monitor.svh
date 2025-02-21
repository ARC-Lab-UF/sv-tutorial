// Greg Stitt
// University of Florida

// In this example, we add the capability of monitoring individual beats and
// entire packets.

`ifndef _AXI4_STREAM_MONITOR_SVH_
`define _AXI4_STREAM_MONITOR_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class axi4_stream_monitor #(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) extends uvm_monitor;
    `uvm_component_param_utils(axi4_stream_monitor#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    virtual axi4_stream_if #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) vif;

    uvm_analysis_port #(axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)) ap;

    // Specifies the transaction level.
    bit is_packet_level;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
        is_packet_level = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);        
        axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) item;
        axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) packet_item;

        // A queue of items used to build a complete packet.
        axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) packet[$];

        forever begin
            @(posedge vif.aclk iff vif.tvalid && vif.tready);
            
            // NOTE: The new has to be done within the loop. The write essentially 
            // sends a pointer instead of a copy, so if we change the data
            // on the next iteration, it could corrupt what has been sent
            // through the analysis port. Instead, we need to make sure that
            // every item sent is a new item. SystemVerilog has garbage
            // collection, so you don't need to worry about deleting the items.

            // Store each individual beat as an item.
            item          = new();
            item.tdata[0] = vif.tdata;
            item.tstrb[0] = vif.tstrb;
            item.tkeep[0] = vif.tkeep;
            item.tlast    = vif.tlast;
            item.tid      = vif.tid;
            item.tdest    = vif.tdest;
            item.tuser    = vif.tuser;

            // If the simulation is at the packet level, push the individual 
            // beat onto the queue until receiving the last beat of the packet.
            if (is_packet_level) begin                
                packet.push_back(item);

                if (vif.tlast) begin
                    // Create and send the entire packet at once.
                    packet_item = new();
                    packet_item.init_from_queue(packet);
                    ap.write(packet_item);

                    // Clear the queue for the next packet.
                    packet.delete();
                end
            end else begin
                // If the transactions are single beats, then send each
                // individual item.
                ap.write(item);
            end
        end
    endtask
endclass

`endif
