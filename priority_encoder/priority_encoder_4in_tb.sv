`timescale 1ns / 100 ps

module priority_encoder_4in_tb;

   logic [3:0] inputs;
   logic [1:0] result_if, result_case, result_case2;
   logic       valid_if, valid_case, valid_case2;
   
   priority_encoder_4in_if UUT_IF (.result(result_if), .valid(valid_if), .*);
   priority_encoder_4in_case UUT_CASE (.result(result_case), .valid(valid_case), .*);
   priority_encoder_4in_case2 UUT_CASE2 (.result(result_case2), .valid(valid_case2), .*);

   initial begin
      for (int i=0; i < 8; i++) begin
	 inputs = i;
	 #10;	 
      end
   end
endmodule

