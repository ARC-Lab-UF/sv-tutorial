// Greg Stitt
// University of Florida

// A UVM environment is essentially the organizational unit that groups together
// all the components involved in verification. In general, the environment 
// create an agents that are needed, creates the scoreboard, and the connects
// the ports that are used within those components. In many cases, an
// environment will also provide configuration options that will make more sense
// once we get to more complex verification examples.
//
// For this example, the environment instantiates the agent and scoreboard (via
// the UVM factory). It also instantiates to uvm_tlm_fifos to connect the ports
// in the agent's monitors with the ports in the scoreboard.

`ifndef _BIT_DIFF_ENV_SVH_
`define _BIT_DIFF_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_agent.svh"
`include "bit_diff_scoreboard.svh"

class bit_diff_env extends uvm_env;
    `uvm_component_utils(bit_diff_env)

    bit_diff_agent agent;
    bit_diff_scoreboard scoreboard;
    
    uvm_tlm_fifo #(int) start_fifo, done_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Create the agent and scoreboard.
        agent = bit_diff_agent::type_id::create("bit_diff_agent", this);
        scoreboard = bit_diff_scoreboard::type_id::create("bit_diff_scoreboard", this);
        
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
