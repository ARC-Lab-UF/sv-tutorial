// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_DRIVER_SVH_
`define _AXI4_STREAM_DRIVER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

class axi4_stream_driver #(
    parameter int DATA_WIDTH = 32
) extends uvm_driver #(axi4_stream_seq_item #(DATA_WIDTH));
    `uvm_component_param_utils(axi4_stream_driver#(DATA_WIDTH))

    virtual axi4_stream_if #(.DATA_WIDTH(DATA_WIDTH)) vif;

    int min_delay, max_delay;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        min_delay = 1;
        max_delay = 1;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void set_delay(int min, int max);
        min_delay = min;
        max_delay = max;
    endfunction

    virtual task run_phase(uvm_phase phase);
        axi4_stream_seq_item #(DATA_WIDTH) req;

        vif.tvalid <= 1'b0;

        // Wait until reset has cleared to start driving.
        @(posedge vif.aclk iff !vif.aresetn);
        @(posedge vif.aclk iff vif.aresetn);
        @(posedge vif.aclk);

        forever begin
            seq_item_port.get_next_item(req);
            vif.tdata  <= req.data;
            vif.tvalid <= 1'b1;
            @(posedge vif.aclk iff vif.tready);
            vif.tvalid <= 1'b0;
            repeat ($urandom_range(min_delay-1, max_delay-1)) @(posedge vif.aclk);
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
