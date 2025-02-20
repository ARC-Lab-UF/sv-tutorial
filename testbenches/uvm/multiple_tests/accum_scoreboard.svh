// Greg Stitt
// University of Florida

// This scoreboard is similar to the previous examples, but includes logic
// to compute the expected output for both single beats and packets.

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
    bit is_packet_level;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        passed = 0;
        failed = 0;
        is_packet_level = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the analysis exports.
        in_ae = new("in_ae", this);
        out_ae = new("out_ae", this);

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
        axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH) in_item;
        axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH) out_item;

        in_item = new();
        out_item = new();
        expected = '0;

        forever begin
            in_fifo.get(in_item);
            // Make sure that the scoreboard is configured to match the items.
            assert (in_item.is_packet_level == is_packet_level);
            out_fifo.get(out_item);

            if (is_packet_level) begin
                // Compute the expected and actual results across the entire
                // packet.
                expected = '0;
                actual = '0;
                foreach (in_item.tdata[i]) expected += in_item.tdata[i];
                foreach (out_item.tdata[i]) actual += out_item.tdata[i];
            end else begin
                // Compute the expected and actual results for each beat.
                actual = out_item.tdata[0];            
                expected += in_item.tdata[0];
            end           

            // Check for errors.
            if (actual === expected) begin
                `uvm_info("SCOREBOARD", $sformatf("Test passed."), UVM_LOW)
                passed++;
            end else begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: result=%0d instead of %0d.", actual, expected))
                failed++;
            end

            // Make sure the last item of each packet asserts tlast.
            if ((is_packet_level || in_item.tlast) && out_item.tlast !== 1'b1) begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: tlast not asserted at end of packet."))
                failed++;
            end

            // Clear the expected at the end of each packet.
            if (in_item.tlast) expected = 0;
        end
    endtask

endclass

`endif
