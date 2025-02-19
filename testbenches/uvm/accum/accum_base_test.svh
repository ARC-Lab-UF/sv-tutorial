// Greg Stitt
// University of Florida

// This file provides a base class for other tests.

`ifndef _ACCUM_BASE_TEST_SVH_
`define _ACCUM_BASE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "accum_env.svh"

class accum_base_test extends uvm_test;
    `uvm_component_utils(accum_base_test)

    accum_env env;

    function new(string name = "accum_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = accum_env::type_id::create("env", this);
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

        // Add coverage summary
        $display("=== Coverage Summary ===\n");
        $display("Input Bin Coverage: %.2f%%", env.input_coverage.input_coverage.get_coverage());
        $display("  In Coverage: %.2f%%", env.input_coverage.input_coverage.in_cp.get_coverage());
        $display("  In Extremes Coverage: %.2f%%", env.input_coverage.input_coverage.in_extremes_cp.get_coverage());

        $display("\nOutput Bin Coverage: %.2f%%", env.output_coverage.output_coverage.get_coverage());

        $display("\nToggle Coverage");
        $display("  In Toggle Coverage: %.2f%%", env.input_coverage.toggle_coverage.toggle_cp.get_coverage());
        $display("  Out Toggle Coverage: %.2f%%", env.output_coverage.toggle_coverage.toggle_cp.get_coverage());

    endfunction

endclass


`endif
