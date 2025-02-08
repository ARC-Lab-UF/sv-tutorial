// Greg Stitt
// University of Florida

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_if.svh"
`include "mult_simple_test.svh"

`timescale 1 ns / 100 ps

module mult_tb #(
    parameter int NUM_TESTS   = 10000,
    parameter bit TOGGLE_READY = 1'b1,

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
        if (!TOGGLE_READY) out_intf.tready <= 1'b0;
        else begin
            forever begin
                out_intf.tready <= $urandom;
                @(posedge clk);
            end
        end
    end 

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
        run_test("mult_simple_test");
    end

    assert property (@(posedge clk) disable iff (rst) !out_intf.tready |=> $stable(out_intf.tdata))
    else `uvm_error("ASSERT", "Output changed with tready disabled.");

    assert property (@(posedge clk) disable iff (rst) !out_intf.tready |=> $stable(out_intf.tvalid))
    else `uvm_error("ASSERT", "Valid changed with tready disabled.");

    // Validate required properties of AXI: once tvalid is asserted, it must remain asserted until
    // tready is asserted.
    assert property (@(posedge clk) disable iff (rst) $fell(out_intf.tvalid) |-> $past(out_intf.tready, 1))
    else `uvm_error("ASSERT", "Output tvalid must be asserted continuously until tready is asserted.");

    // Validate the input interfaces too, even though these are driven by our drivers. This essentially
    // helps ensure that the axi4_stream_driver compiles with AXI standards.
    assert property (@(posedge clk) disable iff (rst) $fell(in0_intf.tvalid) |-> $past(in0_intf.tready, 1))
    else `uvm_error("ASSERT", "In0 tvalid must be asserted continuously until tready is asserted.");

    assert property (@(posedge clk) disable iff (rst) $fell(in0_intf.tvalid) |-> $past(in0_intf.tready, 1))
    else `uvm_error("ASSERT", "In1 tvalid must be asserted continuously until tready is asserted.");

endmodule
