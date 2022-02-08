// Greg Stitt
// University of Florida
//
// This example testbench demonstrates a common non-ideal technique for writing
// testbenches, followed by a much simpler approach. It also illustrates how to
// generate a clock signal, how to change inputs every cycle, how to check
// for correct outputs every cycle, and how to terminate the simulation.

`timescale 1ns / 100 ps

// Module: register_tb1
// Description: A non-ideal testbench for the register module. This is only
// demonstrated for explaining common strategies. I do not recommend the
// strategy presented in this module.

module register_tb1;

   localparam NUM_TESTS = 10000;   
   localparam WIDTH = 8;
   logic clk = 1'b0, rst, en;   
   logic [WIDTH-1:0] in, out;
   logic [WIDTH-1:0] prev_in, prev_out, prev_en;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   // Generate a clock with a 10 ns period
   always begin : generate_clock
      #5 clk = ~clk;
   end

   // A process for driving the inputs.
   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");

      // Reset the register
      rst <= 1'b1;
      in <= '0;      
      en <= 1'b0;

      // Wait 5 cycles
      for (int i=0; i < 5; i++)
        @(posedge clk);

      // Clear reset
      rst <= 1'b0;

      // Generate NUM_TESTS random inputs, once per cycle
      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);
      end
      
      $display("Tests completed.");
      
      // Stops the simulation. $finish can also be used, but will actually
      // exit the simulator, which isn't appropriate when using a GUI.
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
      prev_en = en;
      prev_in = in;
      prev_out = out;
     
      // Give the output time to change. Any amount of time will work as long 
      // as it is less than 1 clock cycle.
      //
      // NOTE: usually if you find yourself waiting for a small amount of time
      // for an output to change, there is usually a better way of writing the 
      // testbench. We'll see those better ways in later examples.
      //
      //#1;
      //#0;
      @(negedge clk);
      
      // If enable was asserted, out should be equal to the previous in.
      if (prev_en && prev_in != out)
        $display("ERROR (time %0t): out = %d instead of %d.", $time, out, prev_in);

      // If enable wasn't asserted, the output shouldn't change.
      if (!prev_en && out != prev_out)
        $display("ERROR (time %0t): out = %d instead of %d.", $time, out, prev_out);     
   end   
endmodule // register_tb


// Module: register_tb2
// Description: A much simpler alternative to the previous testbench that also
// shows how to terminate a simulation without use of $stop or $finish. 

module register_tb2;

   localparam NUM_TESTS = 10000;   
   localparam WIDTH = 8;
   logic clk, rst, en;   
   logic [WIDTH-1:0] in, out;
   logic [WIDTH-1:0] prev_in, prev_out, prev_en;
   
   register #(.WIDTH(WIDTH)) UUT (.*);

   // Here we change the always block to an initial block with an infinite loop.
   // We do this because we will later use a disable statement, which is similar
   // to a break statement. The disable will move execution to the end of the
   // initial block, which breaks the loop.
   initial begin : generate_clock
      clk = 1'b0;
      while(1)
        #5 clk = !clk;
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");

      // Reset the register
      rst <= 1'b1;
      in <= '0;      
      en <= 1'b0;

      // Wait 5 cycles
      for (int i=0; i < 5; i++)
        @(posedge clk);

      // Clear reset
      rst <= 1'b0;

      // Generate NUM_TESTS random inputs, once per cycle
      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;

         // Instead of having one process write some signals, and other process
         // write other signals, we should just have one process write and one
         // process read, and make sure to write using non-blocking assignments.
         prev_en <= en;
         prev_in <= in;
         prev_out <= out;
         @(posedge clk);
      end

      // Disable the other initial blocks so that the simulation terminates.
      // This provides a much cleaner way of ending a simulation, especially
      // when using a GUI.
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
   always begin : check_output
      @(posedge clk);
                
      // If enable was asserted, out should be equal to the previous in.
      if (prev_en && prev_in != out)
        $display("ERROR (time %0t): out = %d instead of %d.", $time, out, prev_in);

      // If enable wasn't asserted, the output shouldn't change.
      if (!prev_en && out != prev_out)
        $display("ERROR (time %0t): out = %d instead of %d.", $time, out, prev_out);     
   end
endmodule // register_tb2
