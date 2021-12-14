`timescale 1ns / 100 ps

module priority_encoder_4in_tb;

   logic [3:0] inputs;
   logic [1:0] result;
   logic       valid;
      
   priority_encoder_4in_if UUT_IF (.*);
   //priority_encoder_4in_case1 UUT_CASE1 (.*);
   //priority_encoder_4in_case2 UUT_CASE2 (.*);
   //priority_encoder_4in_case3 UUT_CASE3 (.*);   
   
   initial begin
      logic [1:0] correct_result;
      logic 	  correct_valid;
      $timeformat(-9, 0, " ns");
                 
      for (int i=0; i < 16; i++) begin
	 inputs = i;
	 #10;

	 for (int j=3; j >= 0; j--) begin
	    if (inputs[i] == 1'b1) begin
	       correct_result = j;
	       break;
	    end	    
	 end

	 correct_valid = inputs != 4'b0;

	 if (result != correct_result)
	   $display("ERROR (time %0t): result = %b instead of %d.", $realtime, result, correct_result);

	 if (valid != correct_valid)
	   $display("ERROR (time %0t): valid = %b instead of %d.", $realtime, valid, correct_valid);	 
      end
   end
endmodule

