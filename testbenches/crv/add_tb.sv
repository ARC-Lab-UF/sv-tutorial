// Greg Stitt
// University of Florida
//
// This file includes a collection of testbenches for the included add module
// that illustrate different coverage strategies.

`timescale 1 ns / 10 ps

class add_item #(int width);
   rand bit [width-1:0] in0;
   rand bit [width-1:0] in1;
   rand bit carry_in;
   rand bit [width-1:0] sum;
   rand bit carry_out;

   constraint c_in0_dist { in0 dist{0 :/ 10, 2**width-1 :/ 10, [1:2**width-2] :/ 80}; }
    
   function void print(); 
      $display("Add Item (Time=%0t): in0=%d, in1=%d, carry_in=%b, sum=%d, carry_out=%b", $time, in0, in1, carry_in, sum, carry_out);      
   endfunction
endclass

// Module: add_tb1
// Description: A testbench that uses cover properties to track whether or not
// specific properties are ever true.
module add_tb1;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);
   
   // The adder doesn't have a clock, but we can still use on in the testbench
   // to coordinate assertion and cover properties.
   logic 	     clk;
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin
      add_item #(.width(WIDTH)) item;
      item = new;      
      $timeformat(-9, 0, " ns");

      for (int i=0; i < NUM_TESTS; i++) begin
	 item.randomize();	 
	 in0 = item.in0;
	 in1 = item.in1;
	 carry_in = item.carry_in;	
	 @(posedge clk);
      end

      $display("Tests completed.");
      disable generate_clock;      
   end

   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);
   
endmodule // add_tb1 


