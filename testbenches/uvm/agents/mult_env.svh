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
    axi4_stream_agent #(2 * mult_tb_pkg::INPUT_WIDTH) agent_out;
    mult_scoreboard scoreboard;

    virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH) in0_vif;
    virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH) in1_vif;
    virtual axi4_stream_if #(2 * mult_tb_pkg::INPUT_WIDTH) out_vif;

    int min_driver_delay;
    int max_driver_delay;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Create the agents and scoreboard.
        agent_in0  = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in0", this);
        agent_in1  = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in1", this);
        agent_out  = axi4_stream_agent#(2 * mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_out", this);
        scoreboard = mult_scoreboard::type_id::create("scoreboard", this);

        if (!uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::get(this, "", "in0_vif", in0_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
        if (!uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::get(this, "", "in1_vif", in1_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
        if (!uvm_config_db#(virtual axi4_stream_if #(2*INPUT_WIDTH))::get(this, "", "out_vif", out_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});

        if (!uvm_config_db#(int)::get(this, "", "min_driver_delay", min_driver_delay)) min_driver_delay = 1;
        if (!uvm_config_db#(int)::get(this, "", "max_driver_delay", max_driver_delay)) max_driver_delay = 1;

    endfunction

    // Connect the monitor and scoreboard ports (the scoreboard internally uses a FIFO).
    function void connect_phase(uvm_phase phase);
        agent_in0.driver.set_delay(min_driver_delay, max_driver_delay);
        agent_in1.driver.set_delay(min_driver_delay, max_driver_delay);

        agent_in0.monitor.ap.connect(scoreboard.in0_ae);
        agent_in1.monitor.ap.connect(scoreboard.in1_ae);
        agent_out.monitor.ap.connect(scoreboard.out_ae);

        agent_in0.driver.vif = in0_vif;
        agent_in0.monitor.vif = in0_vif;
        agent_in1.driver.vif = in1_vif;
        agent_in1.monitor.vif = in1_vif;
        agent_out.driver.vif = out_vif;
        agent_out.monitor.vif = out_vif;
    endfunction

endclass

`endif
