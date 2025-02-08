`ifndef _AXI4_STREAM_MULT_ENV_SVH_
`define _AXI4_STREAM_MULT_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_tb_pkg::*;

`include "axi4_stream_agent.svh"
`include "mult_scoreboard.svh"

class mult_env extends uvm_env;
    `uvm_component_utils(mult_env)

    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in0;
    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in1;
    axi4_stream_agent #(2*mult_tb_pkg::INPUT_WIDTH) agent_out;
    mult_scoreboard scoreboard;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Create the agents and scoreboard.
        agent_in0 = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in0", this);
        agent_in1 = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in1", this);
        agent_out = axi4_stream_agent#(2*mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_out", this);
        scoreboard = mult_scoreboard::type_id::create("scoreboard", this);
    endfunction

    // Connect the monitor and scoreboard ports (the scoreboard internally uses a FIFO).
    function void connect_phase(uvm_phase phase);        
        agent_in0.monitor.ap.connect(scoreboard.in0_ae);
        agent_in1.monitor.ap.connect(scoreboard.in1_ae);
        agent_out.monitor.ap.connect(scoreboard.out_ae);              
    endfunction

endclass
 
`endif
