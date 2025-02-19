// Greg Stitt
// University of Florida

// This file demonstrates various coverage techniques. It has been adapted to
// use axi sequence items from the fully parameterized interface.

`ifndef _ACCUM_COVERAGE_SVH_
`define _ACCUM_COVERAGE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;

// In this example, we need to use the toggle coverage covergroup with two
// different widths. Unfortunately, you can't parameterize a covergroup outside
// of a class, so we create a wrapper class here with its own parameter.
class toggle_coverage #(
    int WIDTH
);
    covergroup cg with function sample (input int index, input bit value);
        index_cp: coverpoint index {
            bins indexes[] = {[0 : WIDTH - 1]};  // Create a dynamic array of bins for bit indices
            option.weight = 0;  // Ignore this in the coverage percentage.
        }

        // Track the value of the bit (whether it's 1 or 0)
        value_cp: coverpoint value {
            bins set = {1}; bins cleared = {0}; option.weight = 0;  // Ignore this in the coverage percentage.
        }

        // Cross coverage between bit index and bit value. This effectively will 
        // test coverage of 0 and 1 for every index we pass in during sampling.
        toggle_cp : cross index_cp, value_cp;
    endgroup

    function new();
        cg = new();
    endfunction
endclass


class accum_input_coverage extends uvm_component;
    `uvm_component_utils(accum_input_coverage)

    typedef axi4_stream_seq_item#(accum_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) axi_item;
    uvm_analysis_export #(axi_item) in_ae;
    uvm_tlm_analysis_fifo #(axi_item) in_fifo;

    logic [accum_tb_pkg::INPUT_WIDTH-1:0] in_data;

    covergroup input_coverage;
        in_cp: coverpoint in_data {option.auto_bin_max = 16;}
        in_extremes_cp: coverpoint in_data {bins zero = {0}; bins max_ = {'1};}
    endgroup

    //in_toggle_coverage toggle_coverage;
    toggle_coverage #(accum_tb_pkg::INPUT_WIDTH) in_toggle_coverage;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        // Instantiate the cover groups.
        input_coverage  = new();
        in_toggle_coverage = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the exports and FIFOs
        in_ae   = new("in_ae", this);
        in_fifo = new("in0_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connect exports to FIFOs
        in_ae.connect(in_fifo.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        axi_item in_item = new();

        forever begin
            // Get data from both inputs.
            in_fifo.get(in_item);
            for (int i = 0; i < in_item.tdata.size(); i++) begin
                in_data = in_item.tdata[i];
                input_coverage.sample();

                // Manually sample each individual bit for toggle coverage.
                for (int j = 0; j < accum_tb_pkg::INPUT_WIDTH; j++) begin
                    in_toggle_coverage.cg.sample(j, in_data[j]);
                end
            end
        end
    endtask
endclass

// Coverage class for output values
class accum_output_coverage extends uvm_component;
    `uvm_component_utils(accum_output_coverage)

    typedef axi4_stream_seq_item#(accum_tb_pkg::OUTPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) axi_item;
    uvm_analysis_export #(axi_item) out_ae;
    uvm_tlm_analysis_fifo #(axi_item) out_fifo;

    logic [accum_tb_pkg::OUTPUT_WIDTH-1:0] output_data;

    covergroup output_coverage;
        output_cp: coverpoint output_data {option.auto_bin_max = 16;}
    endgroup

    toggle_coverage #(accum_tb_pkg::OUTPUT_WIDTH) out_toggle_coverage;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        output_coverage = new();
        out_toggle_coverage = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the export and FIFO
        out_ae   = new("out_ae", this);
        out_fifo = new("out_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connect export to FIFO
        out_ae.connect(out_fifo.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH) out = new();
        forever begin
            out_fifo.get(out);
            for (int i = 0; i < out.tdata.size(); i++) begin
                output_data = out.tdata[i];
                output_coverage.sample();

                // Manually sample each individual bit for toggle coverage.
                for (int j = 0; j < accum_tb_pkg::OUTPUT_WIDTH; j++) begin
                    out_toggle_coverage.cg.sample(j, output_data[j]);
                end
            end
        end
    endtask
endclass

`endif
