// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_DRIVER_SVH_
`define _AXI4_STREAM_DRIVER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
//
// In addition, because uvm_driver has a parameter specifying the sequence
// item, we must provide axi4_stream_seq_item. However, since that seq item
// is now parameterized, we must also provide its parameter value.
class axi4_stream_driver #(
    parameter int DATA_WIDTH = 32
) extends uvm_driver #(axi4_stream_seq_item #(DATA_WIDTH));
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_component_param_utils(axi4_stream_driver#(DATA_WIDTH))

    // We now have a parameterized virtual interface to support different widths.
    virtual axi4_stream_if #(.DATA_WIDTH(DATA_WIDTH)) vif;

    // Configuration parameters.
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

    // Main driving logic.
    virtual task run_phase(uvm_phase phase);
        axi4_stream_seq_item #(DATA_WIDTH) req;

        // According to AXI spec, tvalid must be cleared on reset.
        vif.tvalid <= 1'b0;

        // Wait until reset has cleared to start driving.
        @(posedge vif.aclk iff !vif.aresetn);
        @(posedge vif.aclk iff vif.aresetn);
        @(posedge vif.aclk);

        forever begin
            // Get the sequence item.
            seq_item_port.get_next_item(req);

            // Drive the data onto the tdata port and assert tvalid.
            vif.tdata  <= req.data;
            vif.tvalid <= 1'b1;

            // Hold the data and tvalid until tready is asserted. This is 
            // required by the AXI spec.
            @(posedge vif.aclk iff vif.tready);

            // Clear tvalid for a random amount of cycles to enable more 
            // thorough testing.
            vif.tvalid <= 1'b0;
            repeat ($urandom_range(min_delay-1, max_delay-1)) @(posedge vif.aclk);

            // Tell the sequencer we are done with the seq item.
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
