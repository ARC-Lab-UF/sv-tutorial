// Greg Stitt
// University of Florida

// Like the environment, we actually don't need to change the scoreboard 
// despite the fully parameterized sequence item because the application uses
// default values for all the sideband parameters.

`ifndef _MULT_SCOREBOARD_SVH_
`define _MULT_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class mult_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(mult_scoreboard)

    // Analysis exports (sinks of analysis ports)
    // If our application needed to change the sideband parameters from their
    // defaults, we would have to specify those values every place we use the
    // sequence item type.
    uvm_analysis_export #(axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH)) in0_ae;
    uvm_analysis_export #(axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH)) in1_ae;
    uvm_analysis_export #(axi4_stream_seq_item #(2 * mult_tb_pkg::INPUT_WIDTH)) out_ae;

    // Analysis FIFOs, used to simply synchronization between analysis
    // ports and exports. This basically enables the scoreboard to read
    // from a FIFO, with the FIFO automatically storing monitor data
    // arriving via the analysis ports.
    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH)) in0_fifo;
    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH)) in1_fifo;
    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(2 * mult_tb_pkg::INPUT_WIDTH)) out_fifo;

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
        in0_ae   = new("in0_ae", this);
        in1_ae   = new("in1_ae", this);
        out_ae   = new("out_ae", this);

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
        logic [2*INPUT_WIDTH-1:0] actual, expected;

        // We don't need to specify the sideband parameters because our DUT
        // works with the defaults.
        axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH) in0, in1;
        axi4_stream_seq_item #(2*mult_tb_pkg::INPUT_WIDTH) out;

        // Note that unlike the monitor, which instantiated a new item every
        // iteration, we only need one here because we no longer need the data
        // after pulling it from the FIFO and checking for errors.
        in0 = new();
        in1 = new();

        forever begin
            // Read from the analysis FIFOs to get the two inputs and the
            // actual output.
            in0_fifo.get(in0);
            in1_fifo.get(in1);
            out_fifo.get(out);

            actual = out.tdata;

            // Our model is so simple, we'll just do it here.
            if (is_signed) expected = signed'(in0.tdata) * signed'(in1.tdata);
            else expected = in0.tdata * in1.tdata;

            // Check for errors.
            if (actual == expected) begin
                `uvm_info("SCOREBOARD", $sformatf("Test passed for in0=%0d, in1=%0d.", in0.tdata, in1.tdata), UVM_LOW)
                passed++;
            end else begin
                `uvm_error("SCOREBOARD", $sformatf("Test failed: result=%0d instead of %0d for in0=%0d, in1=%0d", actual, expected, in0.tdata, in1.tdata))
                failed++;
            end
        end
    endtask

endclass

`endif
