`ifndef _AXI4_STREAM_MULT_ENV_SVH_
`define _AXI4_STREAM_MULT_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_agent.svh"
`include "mult_scoreboard.svh"

class axi4_stream_mult_env extends uvm_env;
    `uvm_component_utils(axi4_stream_mult_env)

    axi4_stream_agent agent_in0;
    axi4_stream_agent agent_in1;
    axi4_stream_agent agent_out;
    mult_scoreboard scoreboard;
    
    //uvm_tlm_fifo #(int) start_fifo, done_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Create the agent and scoreboard.
        agent = axi4_stream_agent::type_id::create("axi4_stream_agent", this);
        scoreboard = axi4_stream_scoreboard::type_id::create("axi4_stream_scoreboard", this);
        
        // Create the FIFOs used to communicate between the monitors and scoreboard.
        start_fifo = new("start_fifo", this, 8);
        done_fifo = new("done_fifo", this, 8);
    endfunction

    // Connect the FIFOs to the monitor and scoreboard ports.
    function void connect_phase(uvm_phase phase);        
        agent.start_monitor.start_port.connect(start_fifo.put_export);
        scoreboard.start_port.connect(start_fifo.get_export);
        agent.done_monitor.done_port.connect(done_fifo.put_export);
        scoreboard.done_port.connect(done_fifo.get_export);        
    endfunction

endclass
 
`endif
