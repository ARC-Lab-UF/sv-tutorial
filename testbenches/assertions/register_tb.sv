// Greg Stitt
// University of Florida
//
// This example illustrates how to use assertions to verify the functionality
// of a register. Note how simple the code is compared to the register example
// in the basic/ folder. It is also more powerful since it also checks that the
// reset is working.

`timescale 1 ns / 10 ps

// Module: reigster_tb1
// Description: This module implements a testbench for the register using 
// assertions, with the simplifying assumption that enable is always asserted. 
// The next module will look at how to handle the enable.

module register_no_en_tb_bad #(
    parameter int NUM_TESTS = 10000,
    parameter WIDTH = 8
);
    logic clk, rst, en;
    logic [WIDTH-1:0] in, out;

    register #(
        .WIDTH(WIDTH)
    ) DUT (
        .en(1'b1),
        .*
    );

    // Generate the clock.
    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    // Drive the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1;  // Purposely set to 1 here to expose assertion error.
        en  <= 1'b1;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        // Perform the tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // The following is a potential way to validate the output that was similar
    // to what was shown in the earlier FF example. There is actually one 
    // potential problem with this, which is that it will throw an error if the
    // input is not equal to 0 during reset. This problem occurs because $past
    // still tracks the previous inputs during reset.
    assert property (@(posedge clk) disable iff (rst) out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    // Verify reset.
    assert property (@(posedge clk) rst |=> out == '0);
endmodule


module register_no_en_tb1 #(
    parameter int NUM_TESTS = 10000,
    parameter WIDTH = 8
);
    logic clk, rst, en;
    logic [WIDTH-1:0] in, out;

    register #(
        .WIDTH(WIDTH)
    ) DUT (
        .en(1'b1),
        .*
    );

    // Generate the clock.
    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    // Drive the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1;  // Purposely set to 1 here to expose assertion error.
        en  <= 1'b1;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        // Perform the tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // One potential solution is to extend the disable until the conditions is valid. 
    // Although overkill in this situation, having custom disables for assertions that
    // should only be applied in specific situations is useful.
    logic delayed_rst = 1'b1;
    always_ff @(negedge clk) delayed_rst <= rst;
    assert property (@(posedge clk) disable iff (delayed_rst) out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    // Alternatively, we can use implication to delay the comparison as much as we
    // want. To do this, we need an "antecedent" (i.e. trigger condition) that defines
    // when then condition (or "consequent") should be checked. Note that if the 
    // antecedent is false, the entire implication becomes "vacuously true." This 
    // basically means than if the antecedent is false, we don't care about the
    // consequent. In this case, we want to evaluate the condition every cycle 
    // starting 1 cycle after the reset is cleared. This translates to:
    assert property (@(posedge clk) disable iff (rst) 1 |-> ##1 out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    // or alternatively:
    assert property (@(posedge clk) disable iff (rst) 1 |=> out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    // Normally, you would have a constantly true trigger condition, but it makes
    // sense in this context because without the trigger condition, we can't have
    // the implication, which gives us the ability to ignore one cycle after reset.

    // Alternatively, you could do the following where we basically integrate the
    // "disable iff rst" into the antecedent, which effectively acts as a disable.
    assert property (@(posedge clk) !rst |=> out == $past(in, 1));

    // Verify reset.
    assert property (@(posedge clk) rst |=> out == '0);
endmodule


module register_no_en_tb2 #(
    parameter int NUM_TESTS = 10000,
    parameter WIDTH = 8
);
    logic clk, rst, en;
    logic [WIDTH-1:0] in, out;

    register #(
        .WIDTH(WIDTH)
    ) DUT (
        .en(1'b1),
        .*
    );

    // Generate the clock.
    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    // Drive the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1;  // Purposely set to 1 here to expose assertion error.
        en  <= 1'b1;
        repeat (5) @(posedge clk);

        // Here we clear reset on the rising edge of the clock to demonstrate
        // a weird behavior with the disable construct.
        //@(negedge clk);
        rst <= 1'b0;

        // Perform the tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // Here we have similar solution as the previous example, but to get them not to fail,
    // we need to wait for 2 cycles after reset. After looking over the simulation, the disable
    // is functioning differently than expected. I have yet to verify if this is a simulator
    // bug, or if it is how the SV standard defines the disable.
    //
    // Clearly, each assertion samples values on the rising clock edge. In the code above,
    // the reset is cleared *after* a rising clock edge. However, on the edge where the reset
    // is cleared, these assertions are still being evaluated. This suggests that the disable
    // is evaluating a version of the rst signal that is updated after the cycle on which the
    // values are sampled.
    //
    // There are two ways to fix this: 1) wait two cycles instead of 1 before applying the 
    // consequent, of 2) make sure to clear the disable condition at a time that does not
    // coincide with a clock edge, or 3), change the input during the reset to ensure that
    // this edge case isn't evaluated. In the previous example, we did 2 because we were 
    // clearing reset on a falling clock edge.
    logic [1:0] delayed_rst = '1;
    always_ff @(posedge clk) delayed_rst <= {delayed_rst[0], rst};
    assert property (@(posedge clk) disable iff (delayed_rst[1]) out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    assert property (@(posedge clk) disable iff (rst) 1 |-> ##2 out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    // Interestingly, this assertion still works without changes, which is further evidence that
    // the disable's timing is doing something unexpected.
    assert property (@(posedge clk) !rst |=> out == $past(in, 1));

    // Verify reset.
    assert property (@(posedge clk) rst |=> out == '0);
endmodule


// Module: register_en_tb
// Description: This testbench extends the previous one with an enable, and modifies the 
// input value on reset so that we don't have to deal with the initial assertion failure. 

module register_en_tb #(
    parameter int NUM_TESTS = 10000,
    parameter WIDTH = 8
);
    logic clk, rst, en;
    logic [WIDTH-1:0] in, out;

    register #(.WIDTH(WIDTH)) DUT (.*);

    // Generate the clock.
    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    // Drive the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1'b0;  // Set to 0 to avoid the post-reset assertion failure.
        en  <= 1'b0;
        repeat (5) @(posedge clk);
        rst <= 1'b0;

        // Perform the tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // Notice how simple this testbench is compared to the example in the basic section 
    // of the tutorial. Three lines of code capture the entire behavior of a register.
    assert property (@(posedge clk) disable iff (rst) en |=> out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    assert property (@(posedge clk) disable iff (rst) !en |=> $stable(out));
    assert property (@(posedge clk) rst |=> out == '0);
endmodule
