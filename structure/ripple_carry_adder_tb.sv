// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

module ripple_carry_adder_tb;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 8;  
   logic [WIDTH-1:0] in0, in1, sum, correct_sum;
   logic 	     cin, cout, correct_cout;
         
   ripple_carry_adder UUT (.*);

   initial begin
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 cin = $random;
	 #10;
	 {correct_cout, correct_sum} = in0 + in1 + cin;	 
	 if (sum != correct_sum)
	   $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, correct_sum);      	    

	 if (cout != correct_cout)
	   $display("ERROR (time %0t): cout = %b instead of %b.", $realtime, cout, correct_cout);	  	 
      end

      $display("Tests completed.");      
   end
   
endmodule // ripple_carry_adder_tb
