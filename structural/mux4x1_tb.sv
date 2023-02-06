// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: mux4x1_tb
// Description: Testbench for the mux4x1 module.

module mux4x1_tb;

   logic [3:0] inputs;
   logic [1:0] sel;
   logic       out;

   mux4x1 DUT (.*);

   initial begin
      $timeformat(-9, 0, " ns");
      
      // Iterate over all inputs and select values.
      for (int i=0; i < 2**$bits(inputs); i++) begin
         inputs = i;
         
         for (int j=0; j < 2**$bits(sel); j++) begin
            sel = j;
            #10;
            if (out != inputs[sel])
                $display("ERROR (time %0t): out = %b instead of %b.", $realtime, out, inputs[sel]);                 
         end
      end

      $display("Tests completed.");
   end 
endmodule
   
