// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: alu_tb
// Description: Testbench for alu module.

module alu_tb;

   localparam NUM_TESTS = 10000;   
   localparam WIDTH = 8;   
   logic [WIDTH-1:0] in0, in1, out;
   logic [1:0]       sel;
   logic             neg, pos, zero;
   logic [WIDTH-1:0] correct_out;
   
   alu #(.WIDTH(WIDTH)) DUT (.*);

   // Function to check the status flags
   function void check_flags();
      // Check negative flag.
      if (correct_out[WIDTH-1] != neg)
        $display("ERROR (time %0t): neg = %b instead of %b.", $realtime, neg, correct_out[WIDTH-1]);

      // Check zero flag.
      if ((correct_out == 0) != zero)
        $display("ERROR (time %0t): zero = %b instead of %b.", $realtime, zero, correct_out == 0);

      // Check pos flag.
      if ((signed'(correct_out) > 0) != pos)
        $display("ERROR (time %0t): pos = %b instead of %b.", $realtime, pos, correct_out != 0 && !correct_out[WIDTH-1]);      
   endfunction
       
   initial begin
      $timeformat(-9, 0, " ns");

      // Test NUM_TESTS random inputs and select values.
      for (int i=0; i < NUM_TESTS; i++) begin
         in0 = $random;
         in1 = $random;
         sel = $random;  
         #10;    
         if (sel == 2'b00) correct_out = in0 + in1;
         else if (sel == 2'b01) correct_out = in0 - in1;
         else if (sel == 2'b10) correct_out = in0 & in1;
         else if (sel == 2'b11) correct_out = in0 | in1;

         if (out != correct_out)
              $display("ERROR (time %0t): out = %h instead of %h.", $realtime, out, correct_out);

         if (sel == 2'b00 || sel == 2'b01) check_flags();        
      end 

      $display("Tests completed.");      
   end           
endmodule
