`timescale 1 ns / 10 ps

// Module: ff_tb1
// Description: Testbench for the ff module, which illustrates how to check
// functionality using a simple reference model.

module ff_tb1;

   localparam NUM_TESTS = 1000;      
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.*);

   // Generate a clock with a 10 ns period
   initial begin : generate_clock
      while(1)
	#5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      // Reset the FF
      rst = 1'b1;
      in = 1'b1;      
      en = 1'b0;

      // Wait 5 cycles
      for (int i=0; i < 5; i++)
	@(posedge clk);

      // Clear reset
      rst = 1'b0;

      // Generate NUM_TESTS random inputs and enables, once per cycle
      for (int i=0; i < NUM_TESTS; i++) begin	 
	 in = $random;
	 en = $random;
	 @(posedge clk);
      end

      // Disable the other initial blocks so that the simulation terminates
      disable generate_clock;
      disable check_output;            
      $display("Tests completed.");
   end 
   
   logic prev_out, prev_in, prev_en;

   // Create a simple reference model and compare outputs.
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
      
endmodule


// Module: ff_tb2
// Description: This module implements a testbench for the FF using assertions,
// with the simplifying assumption that enable is always asserted.

module ff_tb2;

   localparam NUM_TESTS = 1000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.en(1'b1), .*);

   initial begin : generate_clock
      while(1)
	#5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst = 1'b1;
      in = 1'b1;      
      en = 1'b0;

      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin	 
	 in = $random;
	 en = $random;
	 @(posedge clk);
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Incorrect attempt 1:
   // ##1 specifes that out should be asserted 1 cycle after in, which is what
   // we want to check. However, the exact meaning of this property is that
   // in should always be asserted and out should be asserted one cycle later.
   //assert property(@(posedge clk) in ##1 out);

   // Incorrect attempt 2:
   // Here we us the implication operator to change the semantics to: if in is
   // asserted, then out should be asserted one cycle later.
   // While closer to what we want, this doesn't include the reset.
   //assert property(@(posedge clk) in |-> ##1 out);
   
   // The following assertion is equivalent to the previous one. |=> is just
   // shorthand for |-> ##1.
   //assert property(@(posedge clk) in |=> out);
   
   // The following is correct because it disables the assertion any time
   // reset is enabled.
   assert property(@(posedge clk) disable iff (rst) in |=> out);
   
   // We should also check to make sure the reset is working correctly.
   // Technically, this is checking for an synchronous reset because it checks
   // to see if out is not asserted on every rising edge that rst is 1.
   assert property(@(posedge clk) rst |-> !out);
   
   // To check for the asynchronous reset, we can use an immediate assertion.
   always @(rst) begin
      // Give the output time to change.
      #1;      
      assert(out == 1'b0);      
   end      
endmodule


// Module: ff_tb3
// Description: This testbench extends the previous one to handle the enable
// and to cover more tests.

module ff_tb3;

   localparam NUM_TESTS = 1000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.*);

   initial begin : generate_clock
      while(1)
	#5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst = 1'b1;
      in = 1'b1;      
      en = 1'b0;
      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin	 
	 in = $random;
	 en = $random;
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
   assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));

   // Here we check to make sure that the output doesn't change when the enable
   // isn't asserted. We can either do this by using the $past function to check
   // the output on the previous cycle, or by using the $stable function, which
   // is semantically equivalent.
   //
   //assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

   // The always block from the previous testbench can be simplified to this:
   always @(rst) #1 assert(out == 1'b0);  
endmodule
