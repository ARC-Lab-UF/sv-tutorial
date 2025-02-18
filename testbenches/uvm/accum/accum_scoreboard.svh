// Greg Stitt
// University of Florida

`ifndef _ACCUM_SCOREBOARD_SVH_
`define _ACCUM_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;

class accum_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(accum_scoreboard)

    uvm_analysis_export #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH)) in_ae;
    uvm_analysis_export #(axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH)) out_ae;

    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH)) in_fifo;
    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH)) out_fifo;

    int passed, failed;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        passed = 0;
        failed = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the analysis exports.
        in_ae   = new("in_ae", this);        
        out_ae   = new("out_ae", this);

        // Create the analysis FIFOs.
        in_fifo = new("in_fifo", this);        
        out_fifo = new("out_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        in_ae.connect(in_fifo.analysis_export);        
        out_ae.connect(out_fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
        logic [accum_tb_pkg::OUTPUT_WIDTH-1:0] actual, expected;
        axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH) in;
        axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH) out;
        
        in = new();
        expected = '0;

        forever begin            
            in_fifo.get(in);            
            out_fifo.get(out);
            actual = out.tdata;

            // Our model is so simple, we'll just do it here.
            expected += in.tdata;

            // Check for errors.
            if (actual == expected) begin
                `uvm_info("SCOREBOARD", $sformatf("Test passed for in=%0d, in1=%0d.", in.tdata, in1.tdata), UVM_LOW)
                passed++;
            end else begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: result=%0d instead of %0d for in=%0d, in1=%0d", actual, expected, in.tdata, in1.tdata))
                failed++;
            end

            if (in.tlast) expected = 0;
        end
    endtask

endclass

`endif
