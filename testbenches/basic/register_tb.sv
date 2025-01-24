// Greg Stitt
// University of Florida
//
// This example testbench demonstrates a common non-ideal technique for writing
// testbenches, followed by a simpler approach. It also illustrates how to
// generate a clock signal, how to change inputs every cycle, how to check
// for correct outputs every cycle, and how to terminate the simulation cleanly.
//
// IMPORTANT: 
// We will soon see that neither of these testbenches are a good way of
// testing a register, so neither of these is recommended. They are instead
// intended to explain basic constructs as we work up to more powerful
// tehcniques.

`timescale 1ns / 100 ps

// Module: register_tb1
// Description: An overly complex testbench for the register module. This is only
// demonstrated for explaining common strategies. I do not recommend the
// strategy presented in this module.

module register_tb1;

    localparam int NUM_TESTS = 10000;
    localparam int WIDTH = 8;
    logic clk = 1'b0, rst, en;
    logic [WIDTH-1:0] in, out;
    logic [WIDTH-1:0] prev_in, prev_out, prev_en;

    register #(.WIDTH(WIDTH)) DUT (.*);

    // Generate a clock with a 10 ns period
    always begin : generate_clock
        #5 clk <= ~clk;
    end

    // A process for driving the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        // Reset the register. Following the advice from the race-condition 
        // examples, reset (and all DUT inputs) are asserted with a 
        // non-blocking assignment.
        rst <= 1'b1;
        in  <= '0;
        en  <= 1'b0;

        // Wait 5 cycles
        repeat (5) @(posedge clk);

        // Clear reset on a falling edge. Not necessary (unless using a blocking
        // assignment), but a common practice.
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Generate NUM_TESTS random inputs, once per cycle
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        $stop;
    end

    always begin : check_output
        // Wait for a rising edge to check the output.
        @(posedge clk);

        // Uncomment to see the value of all signals on each clock edge.
        //
        // The inputs are all the previous values due to the writing process
        // using non-blocking assignments. Use of blocking assignments in the
        // writing process would cause a race condition that could result in
        // non-deterministic behavior.
        //
        // The output has not yet changed at this point because the register
        // uses a non-blocking assignment and this $display reads the value in
        // the same time step. However, even if the circuit wasn't a register and
        // used a blocking assignment, we would again have a race condition
        // because it isn't known whether or not the simulator updates the value
        // of out before it is read here.
        //
        // In either case, we have to wait before getting the new value of out.
        //$display("LOG (time %0t): en = %0b, in = %0d, out = %0d", $time, en, in, out);  

        // Save the previous output value so we can test if en = 0 works.
        prev_en  = en;
        prev_in  = in;
        prev_out = out;

        // Give the output time to change. Any amount of time will work as long 
        // as it is less than 1 clock cycle.
        //
        // IMPORTANT: if you find yourself waiting for a small amount of time
        // for an output to change (outside of combinational logic), there is 
        // usually a better way of writing the testbench. Also, ideally youre
        // testbench shouldn't care if the output is registered or combinational,
        // so we'll see those better ways in later examples.
        //
        //#1;
        //#0;
        @(negedge clk);

        // If enable was asserted, out should be equal to the previous in.
        if (prev_en && prev_in != out) $error("[%0t] out = %d instead of %d.", $time, out, prev_in);

        // If enable wasn't asserted, the output shouldn't change.
        if (!prev_en && out != prev_out) $error("[%0t] out = %d instead of %d.", $time, out, prev_out);
    end
endmodule  // register_tb1


// Module: register_tb2
// Description: A simpler alternative to the previous testbench that also
// shows how to terminate a simulation without use of $stop or $finish. 
//
// This is still not a "good" testbench for a register. We'll see far simpler
// methods in the later examples.

module register_tb2;

    localparam NUM_TESTS = 10000;
    localparam WIDTH = 8;
    logic clk, rst, en;
    logic [WIDTH-1:0] in, out;
    logic [WIDTH-1:0] prev_in, prev_out, prev_en;

    register #(.WIDTH(WIDTH)) DUT (.*);

    // Here we change the always block to an initial block with an infinite loop.
    // We do this because we will later use a disable statement, which is similar
    // to a break statement. The disable will move execution to the end of the
    // initial block, which breaks the loop.
    initial begin : generate_clock
        clk = 1'b0;
        forever #5 clk = !clk;
    end

    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        // Reset the register
        rst <= 1'b1;
        in  <= '0;
        en  <= 1'b0;

        // Wait 5 cycles
        repeat (5) @(posedge clk);

        // Clear reset
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Generate NUM_TESTS random inputs, once per cycle
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;

            // Instead of having one process write some signals, and other process
            // write other signals, we can just have one process write and one
            // process read, and make sure to write using non-blocking assignments.
            // Note that the prev_ version here intentaionally are getting the
            // non-updated values by using non-blocking assignments earlier.
            // It is safe to mix blocking and non-blocking assignments in 
            // testbenches, but any blocking assignments must not be to signals
            // read in another process that is synchronized to the same event.
            prev_en <= en;
            prev_in <= in;
            prev_out <= out;
            @(posedge clk);
        end

        // Disable the other initial blocks so that the simulation terminates.
        disable generate_clock;
        disable check_output;

        $display("Tests completed.");
    end

    // Since we are tracking the previous values, we can just directly compare
    // the output to those values. This is a much cleaner strategy than waiting
    // for the output to change. Basically, instead of preserving values, waiting
    // for output to change, and then comparing, we just save previous values
    // and compare with the current output value. This way, we are always
    // checking outputs on the rising edge.
    //
    // Again, if you ever find yourself having to check a value shortly after a 
    // clock edge to get the right value (or to avoid a race condition), there is
    // almost certainly an easier way to do the testbench.
    always begin : check_output
        @(posedge clk);

        // If enable was asserted, out should be equal to the previous in.
        if (prev_en && prev_in != out) $error("[%0t] out = %d instead of %d.", $time, out, prev_in);

        // If enable wasn't asserted, the output shouldn't change.
        if (!prev_en && out != prev_out) $error("[%0t] out = %d instead of %d.", $time, out, prev_out);
    end
endmodule  // register_tb2
