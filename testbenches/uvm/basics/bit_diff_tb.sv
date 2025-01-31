
// Explanation order:
// bit_diff_tb
// bit_diff_intf
// bit_diff_item

`include "uvm_macros.svh"
`include "bit_diff_if.svh"
//`include "bit_diff_simple_test.svh"

`timescale 1 ns / 100 ps

module bit_diff_tb #(
    parameter int NUM_TESTS = 1000
);
    import uvm_pkg::*;

    bit clk = 1'b0;
    bit rst;

    // Note that I'm not using my normal template here. The reason is that
    // it is pretty widely accepted for complex testbenches to just call
    // $finish to end the simulation, so with UVM, I generally don't bother
    // with a more natural termination.
    always #5 clk <= ~clk;

    initial begin
        rst <= 1'b1;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
    end

    // NOTE: We are using the default WIDTH for now. We'll see why in a later
    // example. Using a parameterized interface in UVM introduces a number of
    // complications that require lengthy explanations.
    bit_diff_if intf (clk);

    bit_diff DUT (
        .clk   (intf.clk),
        .rst   (intf.rst),
        .go    (intf.go),
        .data  (intf.data),
        .result(intf.result),
        .done  (intf.done)
    );

    initial begin
        $timeformat(-9, 0, " ns");

        uvm_config_db#(virtual bit_diff_if)::set(uvm_root::get(), "*", "vif", intf);
        uvm_config_db#(int)::set(uvm_root::get(), "*", "num_tests", NUM_TESTS);

        $dumpfile("dump.vcd");
        $dumpvars;
    end

    // Here we specify which specific test we want to run. run_test() starts 
    // a UVM test. If a parameter is provided, it should be a string specifying
    // the name of the class that corresponds to the test. In general, it is
    // better to not provide a parameter, in which case run_test uses the
    // UVM_TESTNAME environment variable that you can set from the command line, 
    // allowing you to run different tests with the same testbench.
    //
    // Also, by not specifying a parameter, you can actually compile all the 
    // code and then run different combinations of tests to help achieve 100%
    // coverage. Large applications can take a long time to compile, even for
    // simulation, so it can be quite useful to run a bunch of tests in sequence
    // without having to recompile.
    initial begin
        run_test("bit_diff_simple_test");
    end

    // SVAs can be conveniently combined with UVM by the uvm_error macro to record
    // errors. `uvm_error maintains a global error count, no matter where it is
    // is called from. So, as opposed to these assertions causing separate errors
    // from the scoreboard, they just add to the error counts from other places.
    assert property (@(posedge intf.clk) disable iff (intf.rst) intf.go && intf.done |-> !intf.done)
    else `uvm_error("ASSERT", "Done not cleared one cycle after go.");
    assert property (@(posedge intf.clk) disable iff (intf.rst) $fell(intf.done) |-> $past(intf.go, 1))
    else `uvm_error("ASSERT", "Done was cleared without go being asserted");

endmodule
