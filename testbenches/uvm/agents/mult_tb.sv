// Greg Stitt
// University of Florida

// This testbench and associated UVM hierarchy expand on the previous example
// to demonstrate how to handle 1) multiple interface instances, and 
// 2) parameterized interfaces. In turn, we need to parameterize many of the
// classes that are dependent on the interface, which requires some UVM tricks.
// Many people purposely avoid parameterizing UVM classes due to these 
// challenges. We'll look at alternative strategies in later examples, but it
// is important to see how the parameterized strategy works initially.
//
// Another main point of this example is to highlight to code reuse advantages
// of UVM agents when using standard interfaces. This DUT uses three different
// AXI4 streaming interfaces. After we've create the UVM agent for AXI4 
// streaming, we can then reuse that agent across different DUTs that use AXI,
// or different AXI interfaces within the same DUT. This enables huge amount of
// reuse. If your DUT uses standard interfaces for which agents already exist,
// your UVM changes will be limited to application-specific components: tests,
// environments, scoreboards, and sequence items.
//
// Finally this example demonstrates the usage of uvm_analysis_port, whereas
// the previous example used uvm_blocking_put_ports. The biggest difference
// between the two is that the blocking put port is used for communication 
// between one producer and one consumer. Analysis ports allow you to 
// broadcast from one producer to multiple consumers.

`include "uvm_macros.svh"
import uvm_pkg::*;

// Although we could technically parameterize the entire UVM hierarchy, adding
// parameters to the test classes is pretty nasty. Instead we parameterize all
// the classes that depend on the interface parameters. We then define the  
// specific values of each interface's parameters in this package, which can be
// read from the test, env, etc., which don't directly depend on the interface.
import mult_tb_pkg::*;

`include "axi4_stream_if.svh"
`include "mult_simple_test.svh"

`timescale 1 ns / 100 ps

module mult_tb #(
    parameter int NUM_TESTS   = 10000,

    // Enable/disable random toggling of the downstream ready signal.
    parameter bit TOGGLE_READY = 1'b1,

    // This gives us the capability to change the amount of cycles between
    // inputs in the AXI drivers. This is very useful for exposing bugs.
    parameter int MIN_DRIVER_DELAY = 1,
    parameter int MAX_DRIVER_DELAY = 5,

    // Specifies the signedness of the multiplier.
    parameter bit IS_SIGNED = 1'b1
);
    bit clk = 1'b0;
    bit rst;
    bit rst_n = 1'b0;
    always #5 clk <= ~clk;
    assign rst_n = ~rst;

    // Instantiate the three AXI interfaces: 2 input and 1 output. Note that 
    // the output interface has a different width, which prohibits us from 
    // relying on a default value to simplify the UVM code.
    axi4_stream_if #(.DATA_WIDTH(mult_tb_pkg::INPUT_WIDTH)) in0_intf (clk, rst_n);
    axi4_stream_if #(.DATA_WIDTH(mult_tb_pkg::INPUT_WIDTH)) in1_intf (clk, rst_n);
    axi4_stream_if #(.DATA_WIDTH(2 * mult_tb_pkg::INPUT_WIDTH)) out_intf (clk, rst_n);

    // Instantiate the DUT.
    mult #(
        .INPUT_WIDTH(mult_tb_pkg::INPUT_WIDTH),
        .IS_SIGNED(IS_SIGNED)
    ) DUT (
        .aclk      (clk),
        .arst_n    (rst_n),
        .in_tvalid ({in0_intf.tvalid, in1_intf.tvalid}),
        .in_tready ({in0_intf.tready, in1_intf.tready}),
        .in_tdata  ('{in0_intf.tdata, in1_intf.tdata}),
        .out_tvalid(out_intf.tvalid),
        .out_tready(out_intf.tready),
        .out_tdata (out_intf.tdata)
    );

    // Optionally toggle the ready signal randomly.
    initial begin
        if (!TOGGLE_READY) out_intf.tready <= 1'b1;
        else begin
            forever begin
                out_intf.tready <= $urandom;
                @(posedge clk);
            end
        end
    end 

    // Reset the DUT. We do that outside the interfaces in this testbench
    // because there are three separate interfaces, so it isn't clear
    // which one should control the reset.
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
        uvm_config_db#(virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH))::set(uvm_root::get(), "*", "in0_vif", in0_intf);
        uvm_config_db#(virtual axi4_stream_if #(mult_tb_pkg::INPUT_WIDTH))::set(uvm_root::get(), "*", "in1_vif", in1_intf);
        uvm_config_db#(virtual axi4_stream_if #(2 * mult_tb_pkg::INPUT_WIDTH))::set(uvm_root::get(), "*", "out_vif", out_intf);

        // Store the number of tests.
        uvm_config_db#(int)::set(uvm_root::get(), "*", "num_tests", NUM_TESTS);

        // Store the signedness of the multiplier.
        uvm_config_db#(bit)::set(uvm_root::get(), "*", "is_signed", IS_SIGNED);

        // Store configuration info for the drivers.
        uvm_config_db#(int)::set(uvm_root::get(), "*", "min_driver_delay", MIN_DRIVER_DELAY);
        uvm_config_db#(int)::set(uvm_root::get(), "*", "max_driver_delay", MAX_DRIVER_DELAY);
    end

    initial begin
        // Uncomment to run testbench without the makefile
        //run_test("mult_simple_test");

        run_test();
    end

    // Verify that the output doesn't change if the DUT is waiting on the ready flag. 
    // NOTE: AXI is a little weird and prohibits transmitters from waiting on tready
    // to assert tvalid. Normally, a transmitter treats a ready signal as an enable,
    // but that practice is not AXI-compliant.
    assert property (@(posedge clk) disable iff (rst) !out_intf.tready && out_intf.tvalid |=> $stable(out_intf.tdata))
    else `uvm_error("ASSERT", "Output changed with tready disabled.");

    assert property (@(posedge clk) disable iff (rst) !out_intf.tready && out_intf.tvalid |=> $stable(out_intf.tvalid))
    else `uvm_error("ASSERT", "Valid changed with tready disabled.");

endmodule
