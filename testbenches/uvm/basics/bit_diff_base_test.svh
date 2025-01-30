// Greg Stitt
// University of Florida

// Finally, we get to the last class we need, which is a uvm_test. The test
// is the top-level of the UVM hiearchy. In general, a test will instantiate
// and configure the environment based on the needs of the test. It will then
// create some number of sequences that get driven to the DUT, where those
// sequences are configured based on the specifics of each test.
//
// In this file, we don't create an actual test, but instead create a test
// base class that will provide the functionality we need for any other test.
// In this case, that common functionality is creating the environment. It also
// demonstrates other functionality, such as printing the UVM topology and 
// reporting statistics upon completion.

`ifndef _BIT_DIFF_BASE_TEST_SVH_
`define _BIT_DIFF_BASE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_env.svh"

class bit_diff_base_test extends uvm_test;
    `uvm_component_utils(bit_diff_base_test)

    bit_diff_env env;

    function new(string name = "bit_diff_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = bit_diff_env::type_id::create("env", this);        
    endfunction

    virtual function void end_of_elaboration();
        // Prints the UVM topology.
        print();        
    endfunction

    function void report_phase(uvm_phase phase);
        uvm_report_server svr;
        super.report_phase(phase);

        // The report server provides statistics about the simulation.
        svr = uvm_report_server::get_server();
        
        // If there were any instances of uvm_fatal or uvm_error, then we will
        // consider that to be a failed test.
        if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR) > 0) begin
            `uvm_info(get_type_name(), "---------------------------", UVM_NONE)
            `uvm_info(get_type_name(), "---     TEST FAILED     ---", UVM_NONE)
            `uvm_info(get_type_name(), "---------------------------", UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), "---------------------------", UVM_NONE)
            `uvm_info(get_type_name(), "---     TEST PASSED     ---", UVM_NONE)
            `uvm_info(get_type_name(), "---------------------------", UVM_NONE)
        end
    endfunction

endclass


`endif
