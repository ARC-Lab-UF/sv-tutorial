`ifndef _AXI4_STREAM_AGENT_SVH_
`define _AXI4_STREAM_AGENT_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_sequencer.svh"
`include "axi4_stream_driver.svh"
`include "axi4_stream_monitor.svh"

class axi4_stream_agent #(
    parameter int DATA_WIDTH = 32
) extends uvm_agent;
    `uvm_component_param_utils(axi4_stream_agent#(DATA_WIDTH))

    bit is_active;
    axi4_stream_sequencer sequencer;
    axi4_stream_driver #(DATA_WIDTH) driver;
    axi4_stream_monitor #(DATA_WIDTH) monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        is_active = 1'b1;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        sequencer = axi4_stream_sequencer::type_id::create("sequencer", this);
        driver    = axi4_stream_driver#(DATA_WIDTH)::type_id::create("driver", this);
        monitor   = axi4_stream_monitor#(DATA_WIDTH)::type_id::create("monitor", this);
    endfunction
endclass

`endif
