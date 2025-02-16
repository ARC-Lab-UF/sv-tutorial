// Greg Stitt
// University of Florida

// This file provides a base class for other tests.

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

        // Add coverage summary
        $display("=== Coverage Summary ===\n");
        $display("Input Bin Coverage: %.2f%%", env.input_coverage.input_coverage.get_coverage());
        $display("  In0 Coverage: %.2f%%", env.input_coverage.input_coverage.in0_cp.get_coverage());
        $display("  In0 Extremes Coverage: %.2f%%", env.input_coverage.input_coverage.in0_extremes_cp.get_coverage());
        $display("  In1 Coverage: %.2f%%", env.input_coverage.input_coverage.in1_cp.get_coverage());
        $display("  In1 Extremes Coverage: %.2f%%", env.input_coverage.input_coverage.in1_extremes_cp.get_coverage());
        $display("  Cross Coverage: %.2f%%", env.input_coverage.input_coverage.in_cross.get_coverage());

        $display("\nOutput Bin Coverage: %.2f%%", env.output_coverage.output_coverage.get_coverage());

        $display("\nToggle Coverage");
        $display("  In0 Toggle Coverage: %.2f%%", env.input_coverage.in0_toggle_coverage.toggle_cp.get_coverage());
        $display("  In1 Toggle Coverage: %.2f%%", env.input_coverage.in1_toggle_coverage.toggle_cp.get_coverage());


    endfunction

endclass


`endif
