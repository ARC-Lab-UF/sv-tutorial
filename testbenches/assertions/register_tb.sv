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

module register_tb1;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) DUT (.en(1'b1), .*);

   // Generate the clock.
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   // Drive the inputs.
   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst = 1'b1;
      in = 1'b0;      
      en = 1'b1;

      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst = 1'b0;

      // Perform the tests.
      for (int i=0; i < NUM_TESTS; i++) begin    
         in = $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Verify the output:

   // Probably the simplest way of verifying the output. However, this will
   // fail the first test after reset if the input is not equal to the output
   // during reset.
   assert property(@(posedge clk) disable iff (rst) out == $past(in,1));
     
   // Instead of explicitly disabling the check when the reset is asserted, we
   // can use implication to check for the correct output one cycle after
   // every cycle where there isn't a reset.
   assert property(@(posedge clk) rst == 1'b0 |=> out == $past(in,1));
   
   // We should also check to make sure the reset is working correctly.
   // This assertion checks for an synchronous reset because it verifies that
   // out is 0 on every rising edge after rst is 1.
   assert property(@(posedge clk) rst |=> out == '0);
   
   // To check for the asynchronous reset, we can use an immediate assertion.
   always @(rst) #1 assert(out == 1'b0);
endmodule


// Module: register_tb2
// Description: This testbench extends the previous one to handle the enable
// and to cover more tests.

module register_tb2;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;

   // Only used for one of the assertion alternatives.
   logic             output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst = 1'b1;
      in = 1'b0;      
      en = 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst = 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in = $random;
         en = $random;
         @(posedge clk);

         // Only used for one of the assertion examples. Probably not
         // recommended due to the complexity.
         // If we've seen the first enable, then we can enable the output 
         // checker assertion.
         if (first_en) output_check_en = 1'b1;
         // Flag that we've seen the first enable.
         if (en) first_en = 1'b1;         
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
   assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

   // Alternatively, we could replace the separate checks for when en is 1 and
   // 0 by using the enable as a parameter to the past function. However, the
   // past function will return incorrect values until there has been at least
   // one enable, so we need to disable this check until the output is ready.
   // This is probably overkill for this simple example, but can be useful for
   // more complex examples.    
   assert property(@(posedge clk) disable iff (!output_check_en) out == $past(in,1, en));
   
   always @(rst) #1 assert(out == 1'b0);  
endmodule
