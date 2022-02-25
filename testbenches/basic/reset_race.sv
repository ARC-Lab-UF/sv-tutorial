// Greg Stitt
// University of Florida
//
// This example testbench demonstrates a common race condition that can occur
// from incorrect reset code.

`timescale 1ns / 100 ps

// Module: reset_race
// Description: This module demonstrates a common race condition that can occur
// from reset signals. The testbench tests a register, which is included in at
// the bottom of the module.

module reset_race;

   localparam WIDTH = 8;
   bit clk = 1'b0, rst = 1'b1, en = 1'b1;   
   logic [WIDTH-1:0] in = '1, out;
   
   int               zeros = 0;
   int               ones = 0;

   // Toggle the clock.
   initial while (1) #5 clk = ~clk;

   // Toggle the reset every cycle. This is only done to demonstrate the
   // race condition.
   always @(posedge clk) rst = ~rst;
   
   initial begin
      $timeformat(-9, 0, " ns");

      // Check the output of the register on every falling clock edge. We'll see
      // better ways to do this, but we have to give the register time to change
      // its output. 
      for (int i=0; i < 10000; i++) begin         
         @(negedge clk);
         if (out == '0) zeros ++;
         if (out == '1) ones ++;
      end 

      // When I run this in my version of modelsim, I get 5000 0s and 5000 1s.
      // When I change the placement of blocks, I get 10000 0s. In other words,
      // there is clearly a race condition.
      //
      // This race condition occurs because both the changing of the reset
      // and the output of the register are sensitive to the rising edge of the
      // clock. So, when there is a rising edge, the simulator could process the
      // reset's block first, or it could process the register's block first.
      // If the reset is updated first, then the register's block outputs the
      // register's input. If the register's block is processed first, then
      // reset will still be asserted and the register will output 0.
      $display("%d zeros, %d ones", zeros, ones);
      $stop;
   end 

   // The actual register. For this testbench, we move the register code into
   // testbench itself because the race condition wasn't causing errors when
   // the register was in its own file. It also wasn't causing errors when
   // this always block came first in the testbench. As strange as this sounds,
   // it is evidence that simulators can execute always block in any order.
   // Just because your code is working does not mean there aren't race
   // conditions. It just means you might not be exposing them.
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
endmodule


// Module: reset_race_fix
// Description: This module demonstrates that deasserting the reset with a
// non-blocking assignment avoids the race condition.
//
// IMPORTANT:
// Another fix is to only deassert the reset on the falling edge of the clock,
// or any time other than the rising edge. This isn't easy to show in this
// example, but will be used for all future examples.
//
// The falling edge deassertion is technically better because a reset that 
// coincides with a rising clock edge  can cause metastability, which could 
// have an effect on timing simulations. For functional simulations, both
// fixes are equivalent.
//
// A similar issue can potentially occur when reset is assert at time 0. The
// simulator does a bunch of initialization at time 0, so the ordering of that
// initialization and the reset assertion could cause a race condition. The
// solution for asserting reset is to simply use a non-blocking assignment.

module reset_race_fix;

   localparam WIDTH = 8;
   bit clk = 1'b0, rst = 1'b1, en = 1'b1;   
   logic [WIDTH-1:0] in = '1, out;
   
   int               zeros = 0;
   int               ones = 0;


   initial while (1) #5 clk = ~clk;

   // By using a non-blocking assignment, reset gets updated at the end of
   // the time step, so when the register's always block reads reset, it will
   // always be the previous value. This also has the effect of not clearing
   // the reset until the next clock cycle.
   //
   // One way to think of non-blocking assignments that are synchronized to a
   // rising clock edge is that they will always get updated just after the
   // clock, so that anything reading from the modified variables will always
   // get the old value.
   always @(posedge clk) rst <= ~rst;
   
   initial begin
      $timeformat(-9, 0, " ns");

      for (int i=0; i < 10000; i++) begin         
         @(negedge clk);
         if (out == '0) zeros ++;
         if (out == '1) ones ++;
      end 

      $display("%d zeros, %d ones", zeros, ones);
      $stop;
   end 

   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
endmodule
