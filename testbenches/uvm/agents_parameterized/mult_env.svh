// Greg Stitt
// University of Florida

// Interestingly, we don't have to make any changes to our environment despite
// fully parameterizing the agent and sequence item. The reason for the lack of
// changes is that we are using the defaults for all new sideband parameters.
// If our application needed to change them for different interfaces, we would
// have more verbose code, which is explained in the comments below.

`ifndef _MULT_ENV_SVH_
`define _MULT_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class mult_env extends uvm_env;
    `uvm_component_utils(mult_env)

    // Create the agents using parameters specified in mult_tb_pkg.
    // Since we aren't changing the default AXI sideband widths, we are only
    // required to change the WIDTH parameter. 
    //
    // If we needed to change the sideband widths, we would do it like this, 
    // but replacing the defaults with our application-specific values:
    // axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) agent_in0;
    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in0;
    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in1;
    axi4_stream_agent #(2 * mult_tb_pkg::INPUT_WIDTH) agent_out;

    mult_scoreboard scoreboard;

    mult_input_coverage input_coverage;
    mult_output_coverage output_coverage;

    // The virtual interfaces are now fully parameterized, but we again rely on
    // defaults for the sideband interfaces, as opposed to doing something like:
    // virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) in0_vif;
    virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH) in0_vif;
    virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH) in1_vif;
    virtual axi4_stream_if #(2 * mult_tb_pkg::INPUT_WIDTH) out_vif;

    // Configuration information for the drivers.
    int min_driver_delay;
    int max_driver_delay;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Create the agents and scoreboard. Note the use of parameters. If we
        // changed any of the sideband widths from the default for our application,
        // we would also have to make the change here. For example:
        // agent_in0  = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH)::type_id::create("agent_in0", this);

        agent_in0 = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in0", this);
        agent_in1 = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in1", this);
        agent_out = axi4_stream_agent#(2 * mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_out", this);
        scoreboard = mult_scoreboard::type_id::create("scoreboard", this);

        input_coverage = mult_input_coverage::type_id::create("input_coverage", this);
        output_coverage = mult_output_coverage::type_id::create("output_coverage", this);

        // Get the virtual interfaces from the config_db.  Note the use of 
        // parameters. Again, if we change the sideband parameters, we would have
        // to do something like:
        // if (!uvm_config_db#(mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH)::get(this, "", "in0_vif", in0_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});

        if (!uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::get(this, "", "in0_vif", in0_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
        if (!uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::get(this, "", "in1_vif", in1_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
        if (!uvm_config_db#(virtual axi4_stream_if #(2 * INPUT_WIDTH))::get(this, "", "out_vif", out_vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});

        // Read the driver configuration information.
        if (!uvm_config_db#(int)::get(this, "", "min_driver_delay", min_driver_delay)) min_driver_delay = 1;
        if (!uvm_config_db#(int)::get(this, "", "max_driver_delay", max_driver_delay)) max_driver_delay = 1;
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect the virtual interfaces to each agent's driver and monitor.
        agent_in0.driver.vif  = in0_vif;
        agent_in0.monitor.vif = in0_vif;
        agent_in1.driver.vif  = in1_vif;
        agent_in1.monitor.vif = in1_vif;
        agent_out.driver.vif  = out_vif;
        agent_out.monitor.vif = out_vif;

        // Connect the analysis ports (ap) and exports (ae). Note that the
        // scoreboard internally uses analysis FIFOs, so we don't need to
        // setup the FIFOs here like we did in the previous example.
        agent_in0.monitor.ap.connect(scoreboard.in0_ae);
        agent_in1.monitor.ap.connect(scoreboard.in1_ae);
        agent_out.monitor.ap.connect(scoreboard.out_ae);

        // Configure the drivers.
        agent_in0.driver.set_delay(min_driver_delay, max_driver_delay);
        agent_in1.driver.set_delay(min_driver_delay, max_driver_delay);

        // Connect the coverage classes. Note that any analysis port can be
        // send to and consumer.
        agent_in0.monitor.ap.connect(input_coverage.in0_ae);
        agent_in1.monitor.ap.connect(input_coverage.in1_ae);
        agent_out.monitor.ap.connect(output_coverage.out_ae);
    endfunction

endclass

`endif
