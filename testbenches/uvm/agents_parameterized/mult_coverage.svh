// Greg Stitt
// University of Florida

// This file demonstrates various coverage techniques. It has been adapted to
// use axi sequence items from the fully parameterized interface.

`ifndef _MULT_COVERAGE_SVH_
`define _MULT_COVERAGE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_tb_pkg::*;

covergroup toggle_coverage with function sample (input int index, input bit value);
    index_cp: coverpoint index {
        bins indexes[] = {[0 : INPUT_WIDTH - 1]};  // Create a dynamic array of bins for bit indices
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


class mult_input_coverage extends uvm_component;
    `uvm_component_utils(mult_input_coverage)

    // We're going to need to use the fully parameterized sequence item in multiple
    // places, which becomes very verbose. We can simplify it by creating a
    // type for the parameterized sequence item, and then using that type everywhere.
    typedef axi4_stream_seq_item#(mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) axi_item;

    // Analysis exports to receive data from monitors. Note the use of the
    // Note the use of the custom type to make the code more concise.
    uvm_analysis_export #(axi_item) in0_ae;
    uvm_analysis_export #(axi_item) in1_ae;

    // Without the typedef, the above line would look like this:
    // uvm_analysis_port #(axi4_stream_seq_item #(DATA_WIDTH, ID_WIDTH, DEST_WIDTH, USER_WIDTH)) ap;
    //
    // Alternatively, since we are relying on the defaults for the sideband signals, we could still do this:
    //
    // uvm_analysis_port #(axi4_stream_seq_item #(DATA_WIDTH) ap;
    //
    // However, if our application ever used different widths for the sideband
    // signals, the typdef would become more useful.

    // Analysis FIFOs
    uvm_tlm_analysis_fifo #(axi_item) in0_fifo;
    uvm_tlm_analysis_fifo #(axi_item) in1_fifo;

    // Variables to store current input values
    logic [mult_tb_pkg::INPUT_WIDTH-1:0] in0_data;
    logic [mult_tb_pkg::INPUT_WIDTH-1:0] in1_data;

    // Coverage of different input values and combinations.
    covergroup input_coverage;
        in0_cp: coverpoint in0_data {option.auto_bin_max = 8;}
        in1_cp: coverpoint in1_data {option.auto_bin_max = 8;}
        in0_extremes_cp: coverpoint in0_data {bins zero = {0}; bins max_ = {'1};}
        in1_extremes_cp: coverpoint in0_data {bins zero = {0}; bins max_ = {'1};}
        in_cross: cross in0_cp, in1_cp;
    endgroup

    // Create two instance of the toggle_coverage, one for each input.
    // Note we didn't have to do this for input_coverage because covergroups
    // in a class automatically get a variable declared of the same name.
    toggle_coverage in0_toggle_coverage, in1_toggle_coverage;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        // Instantiate the cover groups.
        input_coverage = new();
        in0_toggle_coverage = new();
        in1_toggle_coverage = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Create the exports and FIFOs
        in0_ae   = new("in0_ae", this);
        in1_ae   = new("in1_ae", this);
        in0_fifo = new("in0_fifo", this);
        in1_fifo = new("in1_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connect exports to FIFOs
        in0_ae.connect(in0_fifo.analysis_export);
        in1_ae.connect(in1_fifo.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        axi_item in0 = new();
        axi_item in1 = new();

        forever begin
            // Get data from both inputs.
            in0_fifo.get(in0);
            in1_fifo.get(in1);
            in0_data = in0.tdata;
            in1_data = in1.tdata;
            // Sample the input coverage group.
            input_coverage.sample();

            // Manually sample each individual bit for toggle coverage.
            for (int i = 0; i < INPUT_WIDTH; i++) begin
                in0_toggle_coverage.sample(i, in0_data[i]);
                in1_toggle_coverage.sample(i, in1_data[i]);
            end
        end
    endtask
endclass

// Coverage class for output values
class mult_output_coverage extends uvm_component;
    `uvm_component_utils(mult_output_coverage)

    // We define another axi item here with a different width for the output, while still relying on defaults for the sideband signals.
    typedef axi4_stream_seq_item#(2*mult_tb_pkg::INPUT_WIDTH, axi4_stream_pkg::DEFAULT_ID_WIDTH, axi4_stream_pkg::DEFAULT_DEST_WIDTH, axi4_stream_pkg::DEFAULT_USER_WIDTH) axi_item;

    // Analysis export to receive data from monitor
    uvm_analysis_export #(axi_item) out_ae;

    // Analysis FIFO
    uvm_tlm_analysis_fifo #(axi_item) out_fifo;

    logic [2*mult_tb_pkg::INPUT_WIDTH-1:0] output_data;

    // NOTE: This will only achieve 50% for signed multplication. It is left
    // as an exercise to adjust it for signed products.
    covergroup output_coverage;
        unsigned_cp: coverpoint output_data {option.auto_bin_max = 16;}
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        output_coverage = new();
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
        axi4_stream_seq_item #(2 * mult_tb_pkg::INPUT_WIDTH) out = new();
        forever begin
            out_fifo.get(out);
            output_data = out.tdata;
            output_coverage.sample();
        end
    endtask
endclass

`endif
