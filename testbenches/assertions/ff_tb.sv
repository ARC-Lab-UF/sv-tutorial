// Greg Stitt
// University of Florida

`timescale 1 ns / 10 ps

// Module: ff_no_en_tb
// Description: This module implements a testbench for the FF using assertions,
// with the simplifying assumption that enable is always asserted. 
//
// This example gives an introduction to properties and sequences, which are very 
// powerful constructs. Whereas an immediate assertion uses a normal Boolean 
// expression to determine success/failure, concurrent assertions use properties. 
// Properties are unique because they are essentially Boolean expressions that
// can check conditions across a range of time, where the conditions are generally 
// defined as temporal patterns (i.e., sequences).
//
// Basically, sequences define temporal patterns and properties evaluate the 
// correctness of the behavior of a simulation as defined by the sequences.

module ff_no_en_tb #(
    parameter int NUM_TESTS = 10000
);
    logic clk = 1'b0, rst, en, in, out;

    ff DUT (
        .en(1'b1),
        .*
    );

    initial begin : generate_clock
        forever #5 clk = ~clk;
    end

    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1'b0;
        en  <= 1'b0;

        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            //en <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // Incorrect attempt 1:
    // in ##1 out is a sequence that specifes that out should be asserted 1 cycle 
    // after in is asserted, which is similar to what we want to check. 
    // However, the exact meaning of this property is that in should always be 
    // asserted and out should be asserted one cycle later. 
    //assert property(@(posedge clk) in ##1 out);

    // Incorrect attempt 2:
    // Here we us the implication operator to change the semantics to: if in is
    // asserted, then out should be asserted one cycle later. In this case
    // "##1 out" is a context-dependent sequence that doesn't really make sense
    // by itself, but makes sense within the context of the property.
    // While closer to what we want, this doesn't include the reset because the
    // property will fail during reset.
    //assert property(@(posedge clk) in |-> ##1 out);

    // The following assertion is equivalent to the previous one. |=> is just
    // shorthand for |-> ##1.
    //assert property(@(posedge clk) in |=> out);

    // The following is correct because it disables the assertion any time
    // reset is enabled.
    assert property (@(posedge clk) disable iff (rst) in |=> out);

    // We should also check to make sure the reset is working correctly.
    // Technically, this is checking for an synchronous reset because it checks
    // to see if out is not asserted on every rising edge after rst is 1.
    assert property (@(posedge clk) rst |=> !out);

    // To check for the asynchronous reset, we can use an immediate assertion.
    always @(posedge rst) begin
        // Give the output time to change.
        #1;
        assert (out == 1'b0);
    end
endmodule


// Module: ff_en_tb
// Description: This testbench extends the previous one to handle the enable
// and to cover more tests.

module ff_en_tb #(
    parameter int NUM_TESTS = 10000
);
    logic clk = 1'b0, rst, en, in, out;

    ff DUT (.*);

    initial begin : generate_clock
        forever #5 clk = ~clk;
    end

    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= 1'b0;
        en  <= 1'b0;

        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // The last testbench had one significant weakness, which is that it only
    // checked to see if output was asserted one cycle after the input. To
    // test every situation, we also need to check to see if the output is not
    // asserted one cycle after the input is not asserted. In other words, what
    // we ideally want is to check if the output is equal to the input from one
    // cycle in the past, which we can do with out == $past(in,1).
    // We then just need to add the enable signal and we get a much better
    // assertion.   
    assert property (@(posedge clk) disable iff (rst) en |=> out == $past(in, 1));

    // Here we check to make sure that the output doesn't change when the enable
    // isn't asserted. We can either do this by using the $past function to check
    // the output on the previous cycle, or by using the $stable function, which
    // is semantically equivalent.
    assert property (@(posedge clk) disable iff (rst) !en |=> out == $past(out, 1));
    assert property (@(posedge clk) disable iff (rst) !en |=> $stable(out));

    // The always block from the previous testbench can be simplified to this:
    always @(posedge rst) #1 assert (out == 1'b0);
endmodule
