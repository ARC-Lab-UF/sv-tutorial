// Greg Stitt
// University of Florida

`timescale 1 ns / 10 ps

// Module: structure_tb
// Description: A super basic testbench to provide stimuli to the structure
// module. This testbench does not check for errors. It is intended to be
// used to generate a waveform to see how the width mismatches behave.

module structure_tb;

   logic [31:0] in0, in1;  
   logic [31:0] result1, result2, result3;
   
   structure DUT (.*);

   initial begin
      for (int i=0; i < 100; i++) begin
	 in0 = $random;
	 in1 = $random;
	 #10;	 
      end          
   end      
endmodule
