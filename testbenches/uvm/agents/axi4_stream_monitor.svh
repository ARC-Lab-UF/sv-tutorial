`ifndef _AXI4_STREAM_MONITOR_SVH_
`define _AXI4_STREAM_MONITOR_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

class axi4_stream_monitor #(
    parameter int DATA_WIDTH = 32
) extends uvm_monitor;
    `uvm_component_param_utils(axi4_stream_monitor#(DATA_WIDTH))

    virtual axi4_stream_if #(.DATA_WIDTH(DATA_WIDTH)) vif;

    // Analysis port needs to specify the parameterized sequence item
    uvm_analysis_port #(logic[DATA_WIDTH-1:0]) analysis_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    // The done monitor by using the interface's wait_for_done task.
    task run_phase(uvm_phase phase);
        
    endtask
endclass

`endif
