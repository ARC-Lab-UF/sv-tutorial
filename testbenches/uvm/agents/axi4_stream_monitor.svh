// Greg Stitt
// University of Florida

`ifndef _AXI4_STREAM_MONITOR_SVH_
`define _AXI4_STREAM_MONITOR_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

// To handle different AXI4 stream instances using different widths, we need
// to parameterize this class.
//
// In addition, because uvm_monitor has a parameter specifying the sequence
// item, we must provide axi4_stream_seq_item. However, since that seq item
// is now parameterized, we must also provide its parameter value.
class axi4_stream_monitor #(
    parameter int DATA_WIDTH = 32
) extends uvm_monitor;
    // When using a class with parameters, it has to be registered using
    // uvm_component_param_utils instead of uvm_component_utils. The reason
    // for this is that UVM treats each different parameter value as a
    // separate type.
    `uvm_component_param_utils(axi4_stream_monitor#(DATA_WIDTH))

    // We now have a parameterized virtual interface to support different widths.
    virtual axi4_stream_if #(.DATA_WIDTH(DATA_WIDTH)) vif;

    // We use an analysis port (ap) instead of a blocking put port in this example.
    // Analysis ports are more flexible because they can have multiple 
    // consumers. Note that the analysis port is not connected to anything here.
    // In fact, we have nothing to connect it to because the monitor is part of
    // an agent that is intended to be used across multiple DUTs, multiple 
    // instances of the same DUT, different environments for the same DUT, etc.
    // So, we leave it disconnected and pass the responsibility elsewhere, with
    // the environment normally setting up this connection.
    uvm_analysis_port #(logic[DATA_WIDTH-1:0]) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        // Create the anaylsis port.
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    // Note how simple this monitor is. It simply follows the AXI4 stream spec
    // which states that a transfer occurs when tvalid and tready are both 
    // asserted at the same time. When that handshake occurs, we write the
    // corresponding data to the analyisis port, where it will be later read
    // by the scoreboard. However, it could be read by anything. We don't care
    // what is reading it here. We just send the data and let the environment
    // figure out the different consumers.
    task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.aclk iff vif.tvalid && vif.tready);
            ap.write(vif.tdata);
        end
    endtask
endclass

`endif
