// Greg Stitt
// University of Florida

`ifndef _MULT_BASE_TEST_SVH_
`define _MULT_BASE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "mult_env.svh"

class mult_base_test extends uvm_test;
    `uvm_component_utils(mult_base_test)

    mult_env env;

    function new(string name = "mult_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = mult_env::type_id::create("env", this);        
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
