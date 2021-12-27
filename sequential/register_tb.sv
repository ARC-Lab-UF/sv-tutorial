// Greg Stitt
// University of Florida

`timescale 1ns / 10 ps

// Module: register_tb
// Description: Testbench for the register module. This illustrates how to
// generate a clock signal, how to change inputs every cycle, how to check
// for correct outputs every cycle, and how to terminate the simulation.

module register_tb;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 8;
   logic clk = 1'b0, rst, en;   
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) UUT (.*);

   // Generate a clock with a 10 ns period
   always begin : generate_clock
      #5 clk = ~clk;
   end
   
   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");

      // Reset the register
      rst = 1'b1;
      in = '0;      
      en = 1'b0;

      // Wait 5 cycles
      for (int i=0; i < 5; i++)
	@(posedge clk);

      // Clear reset
      rst = 1'b0;

      // Generate NUM_TESTS random inputs, once per cycle
      for (int i=0; i < NUM_TESTS; i++) begin	 
	 in = $random;
	 en = $random;	 
	 @(posedge clk);
      end
      
      $display("Tests completed.");
      // Stops the simulation. $finish can also be used, but will actually
      // exit the simulator, which isn't appropriate when using a GUI.
      $stop;             
   end 

   logic [WIDTH-1:0] prev_out, prev_in, prev_en;
   
   always begin : check_output
      // On each rising edge, save the previous input and output values.
      @(posedge clk);
      prev_en = en;
      prev_in = in;
      prev_out = out;

      // Give the output time to change
      @(negedge clk);

      // If enable was asserted, out should be equal to the previous in.
      if (prev_en && prev_in != out)
	$display("ERROR (time %0t): out = %d instead of %d.", $realtime, out, prev_in);

      // If enable wasn't asserted, the output shouldn't change.
      if (!prev_en && out != prev_out)
	$display("ERROR (time %0t): out = %d instead of %d.", $realtime, out, prev_out);      
   end   
endmodule // register_tb


// Module: register_tb2
// Description: A modification of the previous testbench to illustrate how to
// terminate simulation without use of $stop or $finish.

module register_tb2;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 8;
   logic clk = 1'b0, rst, en;   
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) UUT (.*);

   // Here we change the always block to an initial block with an infinite loop.
   // We do this because we will later use a disable statement, which is similar
   // to a break statement. The disable will move execution to the end of the
   // initial block, which breaks the loop.
   initial begin : generate_clock
      while(1)
	#5 clk = !clk;
   end
   
   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");            
      rst = 1'b1;
      in = '0;      
      en = 1'b0;
      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin	 
	 in = $random;
	 en = $random;
	 @(posedge clk);
      end

      // disable the other initial blocks so that the simulation terminates
      disable generate_clock;
      disable check_output;            
      $display("Tests completed.");
   end 

   logic [WIDTH-1:0] prev_out, prev_in, prev_en;

   // This block was also converted from an always block to an initial with
   // an infinite loop.
   initial begin : check_output
      while (1) begin
	 @(posedge clk);
	 prev_en = en;
	 prev_in = in;
	 prev_out = out;
	 @(negedge clk);

	 if (prev_en && prev_in != out)
	   $display("ERROR (time %0t): out = %d instead of %d.", $realtime, out, prev_in);

	 if (!prev_en && out != prev_out)
	   $display("ERROR (time %0t): out = %d instead of %d.", $realtime, out, prev_out);

      end
   end   
endmodule // register_tb2
