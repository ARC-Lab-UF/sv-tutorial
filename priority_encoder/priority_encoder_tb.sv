`timescale 1 ns / 100 ps

module priority_encoder_tb;
   
   localparam NUM_INPUTS = 8;   
   logic [NUM_INPUTS-1:0] inputs;
   logic [$clog2(NUM_INPUTS)-1:0] result;
   logic 			  valid;
   
   priority_encoder #(.NUM_INPUTS(8)) UUT (.*);
   
   initial begin
      for (int i=0; i < 2**NUM_INPUTS; i++) begin
	 inputs = i;
	 #10;
      end
   end
   
endmodule
