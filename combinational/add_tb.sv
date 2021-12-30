// Greg Stitt
// University of Florida
// Description: This file provides testbenches for the modules in add.sv.

`timescale 1 ns / 10 ps

module add_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;

   add #(.WIDTH(WIDTH)) UUT (.*);

   initial begin
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 #10;
	 if (sum != in0 + in1)
	   $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, in0+in1); 
      end

      $display("Tests completed.");      
   end  
endmodule // add_tb


module add_carry_out_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out;

   //add_carry_bad #(.WIDTH(WIDTH)) UUT (.*);
   //add_carry_out1 #(.WIDTH(WIDTH)) UUT (.*);
   add_carry_out2 #(.WIDTH(WIDTH)) UUT (.*);

   initial begin
      logic 	   correct_carry_out;
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 correct_carry_out = {{1'b0, in0} + in1}[WIDTH];
	 #10;
	 if (sum != in0 + in1)
	   $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, in0+in1);

	 if (carry_out != correct_carry_out)
	   $display("ERROR (time %0t): carry_out = %d instead of %d.", $realtime, carry_out, correct_carry_out); 
      end

      $display("Tests completed.");      
   end
  
endmodule // add_carry_out_tb


module add_carry_inout_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;

   add_carry_inout #(.WIDTH(WIDTH)) UUT (.*);

   initial begin
      logic 	   correct_carry_out;      
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 correct_carry_out = {{1'b0, in0} + in1 + carry_in}[WIDTH];
	 #10;
	 if (sum != in0 + in1 + carry_in)
	   $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, in0+in1+carry_in);

	 if (carry_out != correct_carry_out)
	   $display("ERROR (time %0t): carry_out = %d instead of %d.", $realtime, carry_out, correct_carry_out); 
      end

      $display("Tests completed.");      
   end
  
endmodule // add_carry_inout_tb


module add_carry_inout_overflow_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in, overflow;

   add_carry_inout_overflow #(.WIDTH(WIDTH)) UUT (.*);

   initial begin
      logic 	   correct_carry_out;
      logic 	   correct_overflow;      
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 correct_carry_out = {{1'b0, in0} + in1 + carry_in}[WIDTH];
	 correct_overflow = (in0[WIDTH-1] == in1[WIDTH-1]) && (correct_carry_out != in0[WIDTH-1]);	 
	 #10;
	 if (sum != in0 + in1 + carry_in)
	   $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, in0+in1+carry_in);

	 if (carry_out != correct_carry_out)
	   $display("ERROR (time %0t): carry_out = %d instead of %d.", $realtime, carry_out, correct_carry_out);

	 if (overflow != correct_overflow)
	   $display("ERROR (time %0t): overflow = %d instead of %d.", $realtime, overflow, correct_overflow); 
      end

      $display("Tests completed.");      
   end
  
endmodule
