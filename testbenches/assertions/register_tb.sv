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

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b1;

      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      // Perform the tests.
      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Verify the output:

   // The following is a potential way to validate the output that was similar
   // to what was shown in the earlier FF example. There is actually one 
   // potential problem with this, which is that it will throw an error if the
   // input is not equal to 0 during reset. This problem occurs because $past
   // still tracks the previous inputs during reset.
   // To see this problem, change the initialization value of in to 1 during
   // reset.
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
   always @(rst) #1 assert(out == '0);
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

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
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

   // For the enable, we can use the same strategy as the FF example.
   // Verify output when enable is asserted.
   assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));

   // Verify output when enable isn't asserted. Only one of these is needed
   // since they are equivalent.
   assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

   // Alternatively, we could replace the separate checks for when en is 1 and
   // 0 by using the enable as a parameter to the past function. However, the
   // past function will return incorrect values until there has been at least
   // one enable, so we need to disable this check until the output is ready.
   // This is probably overkill for this simple example, but can be useful for
   // more complex examples.    
   assert property(@(posedge clk) disable iff (!output_check_en) out == $past(in,1, en));
   
   always @(rst) #1 assert(out == '0);  
endmodule
