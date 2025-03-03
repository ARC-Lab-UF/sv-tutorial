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


// Module: register_tb2
// Description: A simple, but non-ideal testbench for the register module. 
// This is only demonstrated for explaining common non-ideal strategies. I don't 
// recommend the strategy presented in this module.

module register_tb1;

    localparam int NUM_TESTS = 10000;
    localparam int WIDTH = 8;

    // DUT I/O
    logic clk = 1'b0, rst, en;
    logic [WIDTH-1:0] in, out;

    // Used to help with verification.
    logic [WIDTH-1:0] prev_out;

    register #(.WIDTH(WIDTH)) DUT (.*);

    // Generate a clock with a 10 ns period
    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
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
            // $urandom is a convenient function for getting a random 
            // 32-bit number. There is also a $random, but I highly recommend
            // against using it. $random is from an older standard, has less 
            // flexible seeding, and generates far worse distributions.
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);

            // We need to save to previous output to verify that the output
            // doesn't change when enable isn't asserted.
            prev_out = out;

            // We need to wait for some amount of time to allow for the 
            // register's output to change. This has an unattractive side effect
            // of shifting all the subsequent inputs by this amount of time.
            // While it still works, I highly recommend against this strategy.
            // I always try to make all my testbenches do everything on rising
            // clock edges. While that isn't necessary, it is an excellent
            // exercise to understand low-level simulation details.
            #1;

            // Verify the outputs.
            if (en && in != out) $error("out = %d instead of %d.", out, in);
            if (!en && out != prev_out) $error("out changed when en wasn't asserted.");
        end

        $display("Tests completed.");
        disable generate_clock;
    end

endmodule  // register_tb1


// Module: register_tb2
// Description: This testbench separates some of the testing responsibilities
// across to blocks to eliminate the input offsets experienced by the previous
// testbench. This is still an overly complex testbench for the register module, 
// which is only demonstrated for explaining commonly attempted strategies. I do
// not recommend the strategy presented in this module.

module register_tb2;

    localparam int NUM_TESTS = 10000;
    localparam int WIDTH = 8;
    logic clk = 1'b0, rst, en;
    logic [WIDTH-1:0] in, out;
    logic [WIDTH-1:0] prev_in, prev_out, prev_en;

    register #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    // A process for driving the inputs.
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= '0;
        en  <= 1'b0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    initial begin : check_output
        forever begin
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
            //$display("LOG (time %0t): en = %0b, in = %0d, out = %0d", $time, en, in, out);  

            // Save the previous input and output values so we can test en == 0.
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
            if (prev_en && prev_in != out) $error("out = %d instead of %d.", out, prev_in);

            // If enable wasn't asserted, the output shouldn't change.
            if (!prev_en && out != prev_out) $error("out changed when en wasn't asserted.");
        end
    end
endmodule  // register_tb2


// Module: register_tb3
// Description: A simpler alternative to the previous testbench.
// This is still not a good testbench for a register. We'll see far simpler
// methods in the later examples.

module register_tb3;

    localparam NUM_TESTS = 10000;
    localparam WIDTH = 8;
    logic clk = 1'b0, rst, en;
    logic [WIDTH-1:0] in, out;
    logic [WIDTH-1:0] prev_in, prev_out, prev_en;

    register #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        in  <= '0;
        en  <= 1'b0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;

            // Instead of having one process write some signals, and other process
            // write other signals, we can just have one process write and one
            // process read, and make sure to write using non-blocking assignments.
            // Note that the prev_ versions here are intentionally getting the
            // non-updated values by using non-blocking assignments earlier.
            // It is safe to mix blocking and non-blocking assignments in 
            // testbenches, but any blocking assignments must not be to signals
            // read in another process that is synchronized to the same event.
            prev_en <= en;
            prev_in <= in;
            prev_out <= out;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
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
    initial begin : check_output
        forever begin
            @(posedge clk);

            // If enable was asserted, out should be equal to the previous in.
            if (prev_en && prev_in != out) $error("out = %d instead of %d.", out, prev_in);

            // If enable wasn't asserted, the output shouldn't change.
            if (!prev_en && out != prev_out) $error("out changed when en wasn't asserted.");
        end
    end
endmodule  // register_tb3


// Module: register_tb4
// Description: A far simpler alternative to the previous testbenches. This
// version uses a common strategy of separating the responsibilities of the 
// testbench in to separate processes, which results in each process being much
// simpler.
//
// If I had to create a testbench without using any of the more advanced 
// constructs we haven't covered yet, I would likely use this strategy.

module register_tb4;

    localparam NUM_TESTS = 10000;
    localparam WIDTH = 8;
    logic clk=1'b0, rst, en;
    logic [WIDTH-1:0] in, out;
    logic [WIDTH-1:0] expected;

    register #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

    // This example separates responsibilities into different blocks. This block
    // is now simplified and solely provides stimuli to the DUT.
    initial begin : provide_stimulus
        rst <= 1'b1;
        in  <= '0;
        en  <= 1'b0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        repeat (2) @(posedge clk);
        
        for (int i = 0; i < NUM_TESTS; i++) begin
            in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // To simplify the logic of the previous testbenches, we have a separate
    // block whose sole responsibility is to monitor for ouputs and then 
    // determine the correct/expected output each cycle. This code works because
    // on a rising clock edge, neither the input or output has changed values
    // yet. Because the output hasn't changed, we can simply read from out to
    // get the previous output in the case where enable isn't asserted.
    initial begin : monitor        
        forever begin      
            @(posedge clk);      
            expected <= rst ? '0 : en ? in : out;            
        end
    end

    // With the previous process being responsible for determining the expected
    // output, now we can simply compare the actual and expected in this block
    // on every clock edge.
    initial begin : check_outputs        
        forever begin
            @(posedge clk);            
            if (expected != out) $error("Expected=%0h, Actual=%0h", expected, out);            
        end
    end
endmodule 