`timescale 1 ns / 100 ps

module priority_encoder_tb;
   
   localparam NUM_INPUTS = 8;   
   logic [NUM_INPUTS-1:0] inputs;
   logic [$clog2(NUM_INPUTS)-1:0] result;
   logic 			  valid;
   
   priority_encoder #(.NUM_INPUTS(NUM_INPUTS)) UUT (.*);
   
   initial begin
      logic [$clog2(NUM_INPUTS)-1:0] correct_result;
      logic 			     correct_valid;
      $timeformat(-9, 0, " ns");
      
      for (int i=0; i < 2**NUM_INPUTS; i++) begin
	 inputs = i;
	 #10;

	 for (int j=NUM_INPUTS-1; j >= 0; j--) begin
	    if (inputs[j] == 1'b1) begin
	       correct_result = j;
	       break;
	    end	    
	 end

	 correct_valid = inputs != 0;

	 if (result != correct_result)
	   $display("ERROR (time %0t): result = %b instead of %b.", $realtime, result, correct_result);

	 if (valid != correct_valid)
	   $display("ERROR (time %0t): valid = %b instead of %b.", $realtime, valid, correct_valid);	 
      end
   end
   
endmodule
