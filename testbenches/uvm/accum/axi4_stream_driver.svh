// Greg Stitt
// University of Florida

// In this example, we fully parameterize the driver to handle different widths
// for the data and sideband signals.

`ifndef _AXI4_STREAM_DRIVER_SVH_
`define _AXI4_STREAM_DRIVER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

class axi4_stream_driver #(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) extends uvm_driver #(axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH));
    // We need to provide all paramaeters when registering the class.
    `uvm_component_param_utils(axi4_stream_driver#(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH))

    // We now have a fully parameterized virtual interface.
    virtual axi4_stream_if #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) vif;

    // Configuration parameters.
    int min_delay, max_delay;

    bit is_packet_level;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        min_delay = 1;
        max_delay = 1;
        is_packet_level = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void set_delay(int min, int max);
        min_delay = min;
        max_delay = max;
    endfunction

    // Main driving logic.
    virtual task run_phase(uvm_phase phase);   
        // The sequence item also requires all parameters.     
        axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH) req;

        // According to AXI spec, tvalid must be cleared on reset.
        vif.tvalid <= 1'b0;

        // Wait until reset has cleared to start driving.
        @(posedge vif.aclk iff !vif.aresetn);
        @(posedge vif.aclk iff vif.aresetn);
        @(posedge vif.aclk);

        forever begin
            // Get the sequence item.
            seq_item_port.get_next_item(req);

            if (req.is_packet_level) begin
                for (int i=0; i < req.tdata.size(); i++) begin
                    vif.tvalid <= 1'b1;
                    vif.tdata  <= req.tdata[i];
                    vif.tstrb  <= req.tstrb[i];
                    vif.tkeep  <= req.tkeep[i];
                    vif.tlast  <= req.is_packet_level ? i == req.tdata.size()-1 : req.tlast;
                    vif.tid    <= req.tid;
                    vif.tdest  <= req.tdest;
                    vif.tuser  <= req.tuser;
                    @(posedge vif.aclk iff vif.tready);                    

                    vif.tvalid <= 1'b0;
                    repeat ($urandom_range(min_delay - 1, max_delay - 1)) @(posedge vif.aclk);
                end
            end            

            // Tell the sequencer we are done with the seq item.
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
