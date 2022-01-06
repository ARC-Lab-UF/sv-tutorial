// Greg Stitt
// University of Florida
//
// This files provides a basic testbench to demonstrate the gotcha from
// mult_add.sv.

`timescale 1 ns / 10 ps

module mult_add_tb;

   localparam WIDTH = 8;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0]  inputs[4];
   logic [2*WIDTH-1:0] result;
   logic 	       clk;  

   mult_add_bad #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      for (int i=0; i < NUM_TESTS; i++) begin
	 inputs[0] = $random;
	 inputs[1] = $random;
	 inputs[2] = $random;
	 inputs[3] = $random; 	 
	 @(posedge clk);	 
      end

      $display("Tests completed.");      
      disable generate_clock;
   end
   
   assert property (@(posedge clk) result == inputs[0]*inputs[1] + inputs[2]*inputs[3]);   
   
endmodule
