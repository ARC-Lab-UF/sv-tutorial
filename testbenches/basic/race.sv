// Greg Stitt
// University of Florida
//
// This example demonstates critically important race conditions that commonly
// occur in SystemVerilog testbenches. These race conditions cause
// non-deterministic behavior across simulators, possibly even different runs
// of the same simulator.
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
      for (int i=0; i < 10; i++) begin
         x = i;
         @(posedge clk);
      end

      $display("Tests completed.");

      // Stops the simulation. $finish can also be used, but will actually
      // exit the simulator, which isn't appropriate when using a GUI.
      $stop;
   end

   // Verify that x is correct on each cycle.
   // This is an example of non-deterministic behavior. Depending on your
   // simulator, you may get different outcomes ranging from no errors, to
   // every test failing, to some of the tests failing. In my modelsim test,
   // I got the following:
   //
   // # ERROR (time 15 ns): x = 2 instead of 1.
   // # ERROR (time 35 ns): x = 4 instead of 3.
   // # ERROR (time 55 ns): x = 6 instead of 5.
   // # ERROR (time 75 ns): x = 8 instead of 7.
   // # Tests completed.
   //
   // Not only are there errors, but there are errors on alternating tests.
   //
   // This problem occurs because we have to parallel processes where one is
   // writing to x, and one is reading from x. Basically, one a rising clock
   // edge, there is no guarantee that the previous process won't update x
   // before the following process reads the value of x.
   //
   // This issue isn't just a problem for testbenches, it is a general problem 
   // in parallel programming, and is known as a race condition.
   // Basically, a race condition is a situation where behavior depends on
   // the timing of parallel processes. Because those timings can vary, race 
   // conditions can introduce non-determinism.
   initial begin : check_x
      for (int i=0; i < 10; i++) begin
         @(posedge clk);
         if (x != i) $display("ERROR (time %0t): x = %0d instead of %0d.", $time, x, i);
      end            
   end
     
endmodule


// Module: race_fix
// Description: A demonstration of how to fix the race condition.

module race_fix;
   logic clk = 1'b0;
   int x;

   always begin : generate_clock
      #5 clk = ~clk;
   end

   // Generate x=0...9, once per cycle.
   initial begin : drive_x
      $timeformat(-9, 0, " ns");
      for (int i=0; i < 10; i++) begin
         // By simply changing the assignment of x to non-blocking, we
         // eliminate the race condition.
         //
         // The reason this works is that non-blocking assignments get updated
         // at the end of the current time step. So, even if the simulator
         // assigns x here before the reading process reads the value of x,
         // that assignment won't actually take place until the end of the time
         // step, which is after the reads have occurred.
         //
         // GUIDELINE FOR TESTBENCHES: when one process reads a value that a
         // another process writes, the write should use a non-blocking
         // assignment to avoid race conditions.
         x <= i;
         @(posedge clk);
      end

      $display("Tests completed.");
      $stop;
   end

   // Verify that x is correct on each cycle.
   initial begin : check_x
      for (int i=0; i < 10; i++) begin
         @(posedge clk);
         if (x != i) $display("ERROR (time %0t): x = %0d instead of %0d.", $time, x, i);
      end            
   end
     
endmodule
