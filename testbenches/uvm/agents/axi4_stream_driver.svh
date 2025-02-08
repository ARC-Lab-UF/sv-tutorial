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

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        //if (!uvm_config_db#(virtual bit_diff_if)::get(this, "", "vif", vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
    endfunction

    virtual task run_phase(uvm_phase phase);
        axi4_stream_seq_item #(DATA_WIDTH) req;

        //@(posedge vif.aclk iff !vif.aresetn);
        //@(posedge vif.aclk iff vif.aresetn);

        /*repeat (5) @(posedge vif.aclk);
        vif.tdata <= '1;*/
        vif.tvalid <= 1'b0;
        repeat (10) @(posedge vif.aclk);

        forever begin
            seq_item_port.get_next_item(req);
            vif.tdata  <= $urandom; //req.data;
            vif.tvalid <= 1'b1;
            @(posedge vif.aclk iff vif.tready);
            vif.tvalid <= 1'b0;
            repeat ($urandom_range(0, 50)) @(posedge vif.aclk);
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
