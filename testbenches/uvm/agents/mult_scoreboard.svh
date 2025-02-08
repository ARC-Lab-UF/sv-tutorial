// Greg Stitt
// University of Florida

// The scoreboard waits to receive an input from the start monitor and the 
// actual output from the done monitor. It then uses the input to compute the
// expected output. Finally, it compares the expected output with the actual
// output, and reports errors if there are any differences.

`ifndef _MULT_SCOREBOARD_SVH_
`define _MULT_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class mult_scoreboard #(
    parameter int DATA_WIDTH = 32
) extends uvm_scoreboard;
    `uvm_component_param_utils(mult_scoreboard#(DATA_WIDTH))

    uvm_analysis_export #(logic [DATA_WIDTH-1:0]) in0_ae;
    uvm_analysis_export #(logic [DATA_WIDTH-1:0]) in1_ae;
    uvm_analysis_export #(logic [2*DATA_WIDTH-1:0]) out_ae;

    uvm_tlm_analysis_fifo #(logic [DATA_WIDTH-1:0]) in0_fifo;
    uvm_tlm_analysis_fifo #(logic [DATA_WIDTH-1:0]) in1_fifo;
    uvm_tlm_analysis_fifo #(logic [2*DATA_WIDTH-1:0]) out_fifo;

    int passed, failed;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        passed = 0;
        failed = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        in0_ae = new("in0_ae", this);
        in1_ae = new("in1_ae", this);
        out_ae = new("out_ae", this);

        in0_fifo = new("in0_fifo", this);
        in1_fifo = new("in1_fifo", this);
        out_fifo = new("out_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        in0_ae.connect(in0_fifo.analysis_export);
        in1_ae.connect(in1_fifo.analysis_export);
        out_ae.connect(out_fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
        logic [DATA_WIDTH-1:0] in0, in1;
        logic [2*DATA_WIDTH-1:0] actual, expected;

        forever begin
            in0_fifo.get(in0);
            in1_fifo.get(in1);
            out_port.get(actual);

            expected = in0 * in1;
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
