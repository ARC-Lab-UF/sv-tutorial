// Greg Stitt
// University of Florida
//
// This example demonstrates critically important race conditions that commonly
// occur in SystemVerilog testbenches. 
//
// A race condition is a situation where different simulation orders of the
// the same code cause different behaviors. RTL languages do not define a 
// required simulation order, so simulators are free to executes processes 
// in any order. Anything that changes this order (e.g., different simulator, or
// changes to the DUT), can result in the race condition causing errors that
// did not occur previously. 
//
// It is quite common to have unknowingly have race conditions in a simulation 
// that "works," where the races only get exposed at some later point, making 
// you think there is a problem with new code you added, when in reality 
// there was a bug in the testbench all along.
//
// Ultimately, getting the expected simulation output does not mean your code
// code is correct or free from race conditions. I've pointed out race
// conditions to people that refused to change their code because their
// code was "working" before the change. The reality is their code never
// worked correctly. They were just getting lucky. The fact that fixing the
// race condition broke the functionality just proved that the code never
// worked.
//
// It is highly recommended that you fully understand this example before
// moving on to any of the other testbenches.

`timescale 1 ns / 100 ps


// Module: race
// Description: A simple example that demonstrates a common race condition.

module race;
    logic clk = 1'b0;
    int x;

    // Generate a clock with a 10 ns period
    always begin : generate_clock
        #5 clk = ~clk;
    end

    // Generate x=0...9, once per cycle.
    initial begin : drive_x
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 10; i++) begin
            x = i;
            @(posedge clk);
        end

        $display("Tests completed.");

        // Stops the simulation. $finish can also be used, but will actually
        // exit the simulator, which isn't appropriate when using a GUI.
        // In Modelsim/Questa, $finish won't immediate exit the GUI, but
        // will bring up a dialog asking if you want to quit. We'll see how
        // to avoid this in later examples.
        $stop;
    end

    // Verify that x is correct on each cycle.
    // This is an example of non-deterministic behavior. Depending on your
    // simulator, you may get different outcomes ranging from no errors, to
    // every test failing, to some of the tests failing. In my Modelsim/Questa 
    // test, I got the following:
    //
    // # ** Error: [15 ns] x = 2 instead of 1.
    // # ** Error: [35 ns] x = 4 instead of 3.
    // # ** Error: [55 ns] x = 6 instead of 5.
    // # ** Error: [75 ns] x = 8 instead of 7.
    // # Tests completed.
    //
    // Not only are there errors, but there are errors on alternating tests, 
    // which is strange. You would expect all tests in this simple example
    // to either all fail or all succeed.
    //
    // This problem occurs because we have two parallel processes where one is
    // writing to x, and one is reading from x. Remember that simulation order
    // of processes is not defined by our code. So, the simulator can execute
    // the processes in any order it wants. 
    //
    // What is happening here is that two processes are synchronized by a 
    // clock edge, and then resume their functionality. However, we don't 
    // know if drive_x will resume before verify_x. This type of code
    // is often written under the assumption that verify_x resumes first,
    // but that isn't guaranteed. In fact, that isn't happening in the failing
    // tests.
    //
    // The specific errors I reported are occurring because if drive_x resumes
    // before verify_x, it updates x with the next value. Verify_x then resumes
    // and sees an unexpected value, causing the error.
    //
    // This issue isn't just a problem for testbenches, it is a general problem 
    // in parallel programming, and is known as a race condition.
    // Basically, a race condition is a situation where behavior depends on
    // the timing of parallel processes. Because those timings can vary, race 
    // conditions can introduce non-determinism.
    initial begin : verify_x
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            if (x != i) $error("[%0t] x = %0d instead of %0d.", $time, x, i);
        end
    end

endmodule


// Module: race_fix
// Description: A demonstration of how to fix the race condition. 

module race_fix;
    logic clk = 1'b0;
    int x;

    always begin : generate_clock
        #5 clk <= ~clk;
    end

    // Generate x=0...9, once per cycle.
    initial begin : drive_x
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 10; i++) begin
            // By simply changing the assignment of x to non-blocking, we
            // eliminate the race condition.
            //
            // The reason this works is that non-blocking assignments get updated
            // at the end of the current time step. So, even if the simulator
            // assigns x here before the verify_x process reads the value of x,
            // that assignment won't actually take place until the end of the time
            // step, which is after the reads have occurred.
            //
            // Basically, non-blocking assignments ensure that the simulation order
            // does not affect the simulation behavior.
            //
            // GUIDELINE FOR TESTBENCHES: when one process reads a value that a
            // another process writes, and those processes are synchronized by 
            // a common event (e.g., a clock edge), the write should use a 
            // non-blocking assignment to avoid race conditions.
            //
            // IMPORTANT: In the earlier example, I said DUT inputs should always
            // driven with non-blocking assignments. Now we know why. It is very common
            // to assign an input in one process and monitor it another. If the
            // assignment is blocking, then the monitor's behavior will vary depending
            // on which process executes first. 
            x <= i;
            @(posedge clk);
        end

        $display("Tests completed.");
        $stop;
    end

    // Verify that x is correct on each cycle.
    initial begin : verify_x
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            if (x != i) $error("[%0t] x = %0d instead of %0d.", $time, x, i);
        end
    end

endmodule
