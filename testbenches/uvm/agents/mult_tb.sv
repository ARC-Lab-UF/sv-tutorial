// Greg Stitt
// University of Florida

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_if.svh"

`timescale 1 ns / 100 ps

module mult_tb #(
    parameter int NUM_TESTS   = 10000,
    parameter int INPUT_WIDTH = 8
);
    bit clk = 1'b0;
    bit rst;
    always #5 clk <= ~clk;

    axi4_stream_if #(.DATA_WIDTH(INPUT_WIDTH)) in0_intf (clk);
    axi4_stream_if #(.DATA_WIDTH(INPUT_WIDTH)) in1_intf (clk);
    axi4_stream_if #(.DATA_WIDTH(2 * INPUT_WIDTH)) out_intf (clk);

    // Instantiate the DUT.
    mult #(
        .INPUT_WIDTH(INPUT_WIDTH)
    ) DUT (
        .aclk      (clk),
        .arst_n    (!rst),
        .in_tvalid ('{in0_intf.tvalid, in1_intf.tvalid}),
        .in_tready ('{in0_intf.tready, in1_intf.tready}),
        .in_tdata  ('{in0_intf.tdata, in1_intf.tdata}),
        .out_tvalid(out_intf.tvalid),
        .out_tready(out_intf.tready),
        .out_tdata (out_intf.tdata)
    );

    initial begin
        rst <= 1'b1;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Store the virtual interfaces.
        uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::set(uvm_root::get(), "*", "in0_vif", in0_intf);
        uvm_config_db#(virtual axi4_stream_if #(INPUT_WIDTH))::set(uvm_root::get(), "*", "in1_vif", in1_intf);
        uvm_config_db#(virtual axi4_stream_if #(2 * INPUT_WIDTH))::set(uvm_root::get(), "*", "out_vif", out_intf);

        // Store the number of tests.
        uvm_config_db#(int)::set(uvm_root::get(), "*", "num_tests", NUM_TESTS);
    end

    initial begin
        run_test();
    end


endmodule
