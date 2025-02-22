// Greg Stitt
// University of Florida
// Description: This file illustrates four testbenches. The first is a very 
// basic SV testbench for the mux2x1 module. The second demonstrates how to
// test multiple modules that should behave identically. The next two show
// how to use a clock to synchronize responsibilities in a testbench, even one
// for combinational logic. The final one shows how to separate responsibilties
// across multiple blocks, and how to end a simulation without relying on 
// $finish.

// Verilog allows for metricless time literals (e.g. #20 instead of #20ns).
// Unless you want to explicitly specify all units, this requires
// this extra timescale information for the simulator to use a specific scale.
// The first value is time unit (e.g. for 1 ns, #20 = 20 ns)
// The second value is the precision for rounding: 
// e.g. for 1ns/1ns, #0.42 = 0 ns.
//      for 1ns/1ns, #0.65 = 1 ns.
// See the following for more detail:
// https://www.chipverify.com/verilog/verilog-timescale
`timescale 1 ns / 10 ps  // 1 ns time unit, 10 ps precision

// Module: mux2x1_tb
// Description: This module is a basic testbench for the mux2x1 module. It is
// intended to be an intro tutorial to the basic constructs and tools used in
// testbenches.

// The testbench is just a module with no I/O.
module mux2x1_tb;

    // Declare local logic for I/O. I highly suggest using the same name as the 
    // module's I/O when possible to simplify the port connections.
    logic in0, in1, sel, out;

    // Variable to store the correct output for comparison.
    logic correct_out;

    // Define a period of time between tests. Uses specified timescale (ns).
    localparam int period = 10;

    // You can also use the time type to include a specific unit of time if you
    // don't want to use the specified timescale.
    localparam time time_period = 10ns;

    // Instantiate the module we want to test. The typical SV naming convention
    // is DUT for design under test. 
    mux2x1 DUT (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out)
    );

    // I often do this in my testbenches since I always name the local variables
    // the same as the port. However, many people don't like this. I never use it
    // in synthesizable code, but I'll use it in quick testbenches.
    //mux2x1 DUT (.*);

    // Initial is like an always block that only runs once at the beginning of the
    // simulation. Despite only running once, it is quite common to put a loop
    // in the block that does a lot of work.
    // 
    // You don't need a label for the block, but if you have variables declared
    // inside the block, the label will make it easier to find them in your 
    // simulator.
    initial begin : apply_tests
        // When we print messages later on, we will want to display the time.
        // If we don't specify the format, the time won't have any units,
        // and we won't be able to move the cursor to a message in a simulator
        // GUI. In this example, we set the time units to nanosecond scale.
        //
        // See following for formatting:
        // https://www.chipverify.com/verilog/verilog-timeformat
        $timeformat(-9, 0, " ns");

        // Loop over all possible combinations of inputs.       
        for (int i = 0; i < 8; i++) begin

            // Index into the loop counter bits to assign individual inputs.
            // Note that I am using non-blocking assignments here. We could get
            // away with blocking assignments in this example, but driving a DUT
            // with blocking assignments often causes race conditions.
            // TESTBENCH RULE: Only use non-blocking assignments to drive DUT inputs.
            in0 <= i[0];
            in1 <= i[1];
            sel <= i[2];

            // We next need to wait to give the output time to change. I 
            // demonstrate 4 methods below, but you only need one.

            // Wait for the specified amount of time based on the timescale.
            #period;
            // Wait for the specific amount of time.
            #time_period;
            // Or, wait based on an integer literal, where the unit comes from 
            // the timescale.
            #10;
            // Or, wait based on a time literal.
            #10ns;

            // Check for correct output.
            // I'm using a blocking assignment here because I need correct_out to be
            // updated immediately. This has no risk of a race condition because it
            // isn't used anywhere outside this block. In fact, I could ensure that
            // by moving correct_out's declaration inside the initial block. However,
            // that makes it slightly more difficult to include in the waveform.
            correct_out = sel ? in1 : in0;
            if (correct_out != out) begin
                // See following for formatting of $display, $error, etc.:
                // https://www.chipverify.com/verilog/verilog-display-tasks
                $error("[%0t] out = %b instead of %d.", $realtime, out, correct_out);
            end
        end

        $display("Tests completed.");
    end
endmodule


// Most testbenches test a single DUT, but here is an example of testing
// multipe DUTs that should all behave the same.
module mux2x1_all_tb;

    logic in0, in1, sel;
    // We have four modules to test, so we need four outputs.
    logic out_assign, out_if, out_if2, out_case;

    logic correct_out;

    // Instantiate the 4 DUTs.
    mux2x1_assign DUT_ASSIGN (
        .out(out_assign),
        .*
    );
    mux2x1_if DUT_IF (
        .out(out_if),
        .*
    );
    mux2x1_if2 DUT_IF2 (
        .out(out_if2),
        .*
    );
    mux2x1_case DUT_CASE (
        .out(out_case),
        .*
    );

    // We use a function here to avoid copying and pasting for the different DUTs
    function void check_output(string name, logic actual, logic correct);
        if (actual != correct) begin
            $error("[%0t] %s = %b instead of %d.", $realtime, name, actual, correct);
        end
    endfunction

    initial begin
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 8; i++) begin

            in0 <= i[0];
            in1 <= i[1];
            sel <= i[2];
            #10;

            // Verify all the outputs.
            correct_out = sel ? in1 : in0;
            check_output("out_assign", out_assign, correct_out);
            check_output("out_if", out_if, correct_out);
            check_output("out_if2", out_if2, correct_out);
            check_output("out_case", out_case, correct_out);
        end

        $display("Tests completed.");
    end
endmodule


// This testbench demonstrates how to synchronize tests with a clock, which is
// a common strategy even for combinational DUTs.
module mux2x1_tb2;

    logic in0, in1, sel, out;
    logic correct_out;

    // Here we use a clock for synchronizing the testbench, even though the
    // DUT does not require one.
    logic clk = 1'b0;

    mux2x1 DUT (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out)
    );

    // Generate a clock with a separate always block. We'll see a slightly better
    // way of doing this in the next testbench.
    always begin : generate_clock
        forever #5 clk <= !clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 8; i++) begin

            in0 <= i[0];
            in1 <= i[1];
            sel <= i[2];

            // Here we wait for a rising clock edge (or a full clock period)
            // in between tests. There isn't a strong reason to use a clock
            // in this example, but it becomes more useful when synchronizing
            // multiple processing in the same testbench, as shown in the next
            // testbench.
            @posedge(clk);

            correct_out = sel ? in1 : in0;
            if (correct_out != out) begin
                $error("[%0t] out = %b instead of %d.", $realtime, out, correct_out);
            end
        end

        $display("Tests completed.");

        // An RTL simulation finishes on its own when there are no more events
        // to simulate. Because we use an always block to toggle the clock, 
        // there will always be events to simulate, so it the simulation will
        // never stop on its own. We can force it to stop with either $stop or
        // $finish.
        // $stop pauses a simulation, usually so it can be debugged and resumed.
        // $finish will terminate the simulation. If you are using Modelsim or
        // Questa, $finish will ask you if you want to exit. 
        //$stop; 
        $finish;
    end
endmodule

// In this testbench, we separate the responsibilities across multiple blocks,
// which makes the clock synchronization more useful. It also demonstrates how
// to more gracefully end a simulation by disabling the clock generation, as
// opposed to calling $finish. For more complex testbenches, it becomes more
// difficult to achieve this graceful finish, so it is perfectly acceptable to
// just use $finish.
module mux2x1_tb3;

    logic in0, in1, sel, out;
    logic correct_out;
    logic clk = 1'b0;

    mux2x1 DUT (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out)
    );

    // We now use an initial block with a forever loop, which enables us to
    // disable the block at the end of the simulation. The simulation then
    // ends a little more gracefully than calling $finish.
    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

    // More advanced testbenches often use many blocks with different 
    // responsibilities. We imitate that here with a block that solely drives
    // the DUT with different input stimuli.
    initial begin : provide_stimulus
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 8; i++) begin
            in0 <= i[0];
            in1 <= i[1];
            sel <= i[2];
            @posedge(clk);
        end

        $display("Tests completed.");

        // In this example, we disable the clock generation, which causes the
        // simulation to finish with having to call $finish.
        disable generate_clock;
    end

    // We've separated the responsibility of verifying the output from the
    // previous block into this block, and use the rising edge of the clock
    // to synchronize the stimuli and verification. This is a common testbench
    // strategy we'll see as we get to more advanced techniques.
    initial begin : verify_output
        forever begin
            @(posedge clk);
            correct_out = sel ? in1 : in0;
            if (correct_out != out) begin
                $error("[%0t] out = %b instead of %d.", $realtime, out, correct_out);
            end
        end
    end
endmodule