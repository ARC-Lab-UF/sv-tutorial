// Greg Stitt
// University of Florida

// This class defines the environment for testing the AXI4 stream multiplier.
// The environment is where most of the application-specific set up occurs.
// The environment first instantiates the three agents needed by the DUT, 
// along with a scoreboard. It is also respondible for obtaining the virtual
// interfaces from the config_db and connecting them to the corresponding 
// agents. Finally, it also configures the drivers with specific timing
// information to enable more flexible testing.

`ifndef _MULT_ENV_SVH_
`define _MULT_ENV_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_tb_pkg::*;

`include "axi4_stream_agent.svh"
`include "mult_scoreboard.svh"
`include "mult_coverage.svh"

// Note that the environment is not parameterized. We could make it parameterized,
// but then we would also have to parameterize the tests, which involves some
// weird tricks. Usually a good compromise is to parameterize the more general
// purpose classes, such as the agents, which can be instantiated with many
// different parameter values. The test and environment then use values defined
// in mult_tb_pkg. While this package prevents changes to the parameters without
// recompiling, it is considerably simpler than fully parameterizing the entire
// UVM hierarchy.

class mult_env extends uvm_env;
    `uvm_component_utils(mult_env)

    // Create the agents using parameters specified in mult_tb_pkg.
    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in0;
    axi4_stream_agent #(mult_tb_pkg::INPUT_WIDTH) agent_in1;
    axi4_stream_agent #(2 * mult_tb_pkg::INPUT_WIDTH) agent_out;

    // Note that the scoreboard is application specific, and is therefore named
    // mult instead of axi4_stream.
    mult_scoreboard scoreboard;

    // Coverage classes that will receive inputs and outputs from the monitors.
    mult_input_coverage input_coverage;
    mult_output_coverage output_coverage;

    // The virtual interfaces are now parameterized based of the mult_tb_pkg constants.
    // Also, in the previous example, we had the driver and monitor retrieve the
    // virtual interfaces directly from the config_db. When using multiple agents,
    // we can't do that because each agent instance doesn't know they name to
    // look up in the config_db. Only the environment and test have that information.
    // So, the environment now grabs these from the config_db and connects them
    // to the agents.
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
        // Create the agents and scoreboard. Note the use a parameters.
        agent_in0  = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in0", this);
        agent_in1  = axi4_stream_agent#(mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_in1", this);
        agent_out  = axi4_stream_agent#(2 * mult_tb_pkg::INPUT_WIDTH)::type_id::create("agent_out", this);
        scoreboard = mult_scoreboard::type_id::create("scoreboard", this);

        input_coverage = mult_input_coverage::type_id::create("input_coverage", this);
        output_coverage = mult_output_coverage::type_id::create("output_coverage", this);

        // Get the virtual interfaces from the config_db.  Note the use of 
        // parameters. Different parameter values correspond to
        // different types in the database, so we need to provide the values.
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
