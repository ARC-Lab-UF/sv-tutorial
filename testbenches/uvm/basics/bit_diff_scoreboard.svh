// Greg Stitt
// University of Florida

// The scoreboard waits to receive an input from the start monitor and the 
// actual output from the done monitor. It then uses the input to compute the
// expected output. Finally, it compares the expected output with the actual
// output, and reports errors if there are any differences.

`ifndef _BIT_DIFF_SCOREBOARD_SVH_
`define _BIT_DIFF_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import bit_diff_if_pkg::*;

class bit_diff_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(bit_diff_scoreboard)

    // Ports for communicating with the monitors.
    uvm_blocking_get_port #(int) start_port, done_port;
    int passed, failed;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        passed = 0;
        failed = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        start_port = new("start_port", this);
        done_port  = new("done_port", this);
    endfunction

    // Reference model for computing the expected output.
    function automatic int model(int data, int width = bit_diff_if_pkg::WIDTH);
        int diff = 0;
        for (int i = 0; i < width; i++) begin
            diff = data[0] ? diff + 1 : diff - 1;
            data = data >> 1;
        end
        return diff;
    endfunction

    virtual task run_phase(uvm_phase phase);        
        int input_data, actual, expected;

        forever begin
            // Wait to receive the input from the start monitor and the actual
            // output from the done monitor.
            start_port.get(input_data);
            done_port.get(actual);

            expected = model(input_data);
            if (actual == expected) begin
                `uvm_info("SCOREBOARD", $sformatf("Test passed for data=h%h.", input_data), UVM_LOW)
                passed++;
            end else begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: result=%0d instead of %0d for data=h%h", actual, expected, input_data))
                failed++;
            end
        end
    endtask

endclass

`endif
