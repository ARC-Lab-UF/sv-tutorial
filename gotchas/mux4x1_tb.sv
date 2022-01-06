// Greg Stitt
// University of Florida
//
// This file provides a testbench for the gotcha in the mux4x1 module, while
// also demonstrating a gotcha that can occur in testbenches.
//
// Note that when running this testbench in the provided form, there will be
// no errors reported, which is the gotcha. If you look at the waveform, there
// are clearly errors. Read below for the explanation and fix.

`timescale 1 ns / 100 ps

// Module: mux4x1_tb
// Description: Testbench for the mux4x1 module.

module mux4x1_tb;

   localparam WIDTH = 8;
   localparam NUM_TESTS = 100;   
   logic [WIDTH-1:0] inputs[4];
   logic [1:0] sel;
   logic [WIDTH-1:0] out;

   mux4x1 #(.WIDTH(WIDTH)) DUT (.*);

   initial begin
      $timeformat(-9, 0, " ns");

      for (int i=0; i < NUM_TESTS; i++) begin
	 for (int j=0; j < 4; j++) begin
	    inputs[j] = $random;	    
	 end
	 sel = $random;
	 #10;

	 // The following doesn't catch any of the errors. To see there are
	 // errors, look at the waveform and see that whenever sel == 2'b00
	 // the output is all Xs. Clearly inputs[sel] is never equal to all Xs
	 // so why is this condition reporting that they are in fact equal?
	 //
	 // GOTCHA: there are multiple comparison operators in SV.
	 // == and != will return Xs if there are Xs in either input to the
	 // comparison. In a boolean condition, an X will be treated as 0, or
	 // false. Therefore, despite the fact that the values being compared
	 // are not equal, this condition will actually be false.	
	 if (out != inputs[sel])
	   $display("ERROR (time %0t): out = %b instead of %b.", $realtime, out, inputs[sel]);

	 // To fix the issue, we need to use the === or !== comparison 
	 // operators. These comparison will do a literal comparision, so Xs
	 // will be treated as a unique value. For example, comparing Xs will
	 // be true, but comparing Xs and anything else will be false.
	 // We can therefore fix the testbench by just doing the != as an !==.
	 // Uncomment the following to see the printing of the errors.
	 //
	 //if (out !== inputs[sel])
	 //  $display("ERROR (time %0t): out = %b instead of %b.", $realtime, out, inputs[sel]);
      end
   end 
endmodule // mux4x1_tb

   
