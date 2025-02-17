// Greg Stitt
// University of Florida

`ifndef _ACCUM_ENV_SVH_
`define _ACCUM_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;
import axi4_stream_pkg::*;

`include "axi4_stream_agent.svh"
`include "accum_scoreboard.svh"
`include "accum_coverage.svh"

class accum_env extends uvm_env;
    `uvm_component_utils(accum_env)

    axi4_stream_agent #(accum_tb_pkg::INPUT_WIDTH) agent_in;    
    axi4_stream_agent #(accum_tb_pkg::OUTPUT_WIDTH) agent_out;

    accum_scoreboard scoreboard;

    //accum_input_coverage input_coverage;
    //accum_output_coverage output_coverage;

    virtual axi4_stream_if #(accum_tb_pkg::INPUT_WIDTH) in_vif;    
    virtual axi4_stream_if #(accum_tb_pkg::OUTPUT_WIDTH) out_vif;

    // Configuration information for the drivers.
    int min_driver_delay;
    int max_driver_delay;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);        
        agent_in = axi4_stream_agent#(accum_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in", this);        
        agent_out = axi4_stream_agent#(accum_tb_pkg::OUTPUT_WIDTH)::type_id::create("agent_out", this);
        scoreboard = mult_scoreboard::type_id::create("scoreboard", this);

        //input_coverage = mult_input_coverage::type_id::create("input_coverage", this);
        //output_coverage = mult_output_coverage::type_id::create("output_coverage", this);

        if (!uvm_config_db#(virtual axi4_stream_if #(accum_tb_pkg::INPUT_WIDTH))::get(this, "", "in_vif", in_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});        
        if (!uvm_config_db#(virtual axi4_stream_if #(accum_tb_pkg::OUTPUT_WIDTH))::get(this, "", "out_vif", out_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});

        // Read the driver configuration information.
        if (!uvm_config_db#(int)::get(this, "", "min_driver_delay", min_driver_delay)) min_driver_delay = 1;
        if (!uvm_config_db#(int)::get(this, "", "max_driver_delay", max_driver_delay)) max_driver_delay = 1;
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect the virtual interfaces to each agent's driver and monitor.
        agent_in.driver.vif  = in0_vif;
        agent_in.monitor.vif = in0_vif;        
        agent_out.driver.vif  = out_vif;
        agent_out.monitor.vif = out_vif;

        // Connect the analysis ports (ap) and exports (ae). Note that the
        // scoreboard internally uses analysis FIFOs, so we don't need to
        // setup the FIFOs here like we did in the previous example.
        agent_in.monitor.ap.connect(scoreboard.in0_ae);
        agent_out.monitor.ap.connect(scoreboard.out_ae);

        // Configure the driver.
        agent_in.driver.set_delay(min_driver_delay, max_driver_delay);
        
        // Connect the coverage classes. Note that any analysis port can be
        // send to and consumer.
        agent_in.monitor.ap.connect(input_coverage.in0_ae);        
        agent_out.monitor.ap.connect(output_coverage.out_ae);
    endfunction

endclass

`endif
