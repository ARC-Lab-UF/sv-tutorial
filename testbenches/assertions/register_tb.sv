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


module register_no_en_tb #(
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
    logic [1:0] delayed_rst = '1;
    always_ff @(posedge clk) delayed_rst <= {delayed_rst[0], rst};
    assert property (@(posedge clk) disable iff (delayed_rst[1]) out == $past(in, 1))
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


// Module: register_en_tb
// Description: This testbench extends the previous with an enable

module register_en_tb #(
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
    
    // We don't need a specialized disable or antecedent here because we now have the en.
    assert property (@(posedge clk) disable iff (rst) en |=> out == $past(in, 1))
    else $error("[%0t] actual = %0d, expected = %0d", $realtime, $sampled(out), $past(in, 1));

    assert property (@(posedge clk) disable iff (rst) !en |=> $stable(out));

    // Verify reset.
    assert property (@(posedge clk) rst |=> out == '0);
endmodule
