// Greg Stitt
// University of Florida

// This scoreboard uses analysis exports and FIFOs to receive data from the
// different agent monitors.

`ifndef _MULT_SCOREBOARD_SVH_
`define _MULT_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_tb_pkg::*;

// The scoreborad is not parameterized. It only needs a single input width, so
// it is easier to just get that from mult_tb_pkg. It could easily parameterized
// with the environment providing the parameter, but there is no real advantage
// to doing so.
class mult_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(mult_scoreboard)

    // Analysis exports (sinks of analysis ports)
    uvm_analysis_export #(logic [mult_tb_pkg::INPUT_WIDTH-1:0]) in0_ae;
    uvm_analysis_export #(logic [mult_tb_pkg::INPUT_WIDTH-1:0]) in1_ae;
    uvm_analysis_export #(logic [2*mult_tb_pkg::INPUT_WIDTH-1:0]) out_ae;

    // Analysis FIFOs, used to simply synchronization between analysis
    // ports and exports. This basically enables the scoreboard to read
    // from a FIFO, with the FIFO automatically storing monitor data
    // arriving via the analysis ports.
    uvm_tlm_analysis_fifo #(logic [mult_tb_pkg::INPUT_WIDTH-1:0]) in0_fifo;
    uvm_tlm_analysis_fifo #(logic [mult_tb_pkg::INPUT_WIDTH-1:0]) in1_fifo;
    uvm_tlm_analysis_fifo #(logic [2*mult_tb_pkg::INPUT_WIDTH-1:0]) out_fifo;

    int passed, failed;
    bit is_signed;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        passed = 0;
        failed = 0;

        // Get signed status to calculate the expected output.
        if (!uvm_config_db#(bit)::get(this, "", "is_signed", is_signed)) `uvm_fatal("NO_IS_SIGNED", "is_signed not specified.");
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the analysis exports.
        in0_ae = new("in0_ae", this);
        in1_ae = new("in1_ae", this);
        out_ae = new("out_ae", this);

        // Create the analysis FIFOs.
        in0_fifo = new("in0_fifo", this);
        in1_fifo = new("in1_fifo", this);
        out_fifo = new("out_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect the FIFOs to the analysis exports. This basically enables
        // us to simply read from the FIFO to get data send from analsis ports.
        in0_ae.connect(in0_fifo.analysis_export);
        in1_ae.connect(in1_fifo.analysis_export);
        out_ae.connect(out_fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
        logic [INPUT_WIDTH-1:0] in0, in1;
        logic [2*INPUT_WIDTH-1:0] actual, expected;

        forever begin
            // Read from the analysis FIFOs to get the two inputs and the
            // actual output.
            in0_fifo.get(in0);
            in1_fifo.get(in1);
            out_fifo.get(actual);

            // Our model is so simple, we'll just do it here.
            if (is_signed) expected = signed'(in0) * signed'(in1);
            else expected = in0 * in1;

            // Check for errors.
            if (actual == expected) begin
                `uvm_info("SCOREBOARD", $sformatf("Test passed for in0=%0d, in1=%0d.", in0, in1), UVM_LOW)
                passed++;
            end else begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: result=%0d instead of %0d for in0=%0d, in1=%0d", actual, expected, in0, in1))
                failed++;
            end
        end
    endtask

endclass

`endif
