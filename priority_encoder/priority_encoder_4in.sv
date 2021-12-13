// Greg Stitt
// University of Florida

module priority_encoder_4in_if
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb
     begin	
	valid = 1'b1;
	result = 2'b00;
	
	if (inputs[3] == 1'b1)
	  result = 2'b11;
	else if (inputs[2] == 1'b1)
	  result = 2'b10;
	else if (inputs[1] == 1'b1)
	  result = 2'b01;
	else if (inputs[0] == 1'b1)
	  result = 2'b00;
	else
	  valid = 1'b0;             	
     end
endmodule // priority_encoder_4in_if


module priority_encoder_4in_case
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb
     begin
	valid = 1'b1;
	
	case (inputs)
	  4'b0000 : begin result = 2'b00; valid = 1'b0; end
	  4'b0001 : result = 2'b00;
	  4'b0010 : result = 2'b01;
	  4'b0011 : result = 2'b01;
	  4'b0100 : result = 2'b10;
	  4'b0101 : result = 2'b10;
	  4'b0110 : result = 2'b10;
	  4'b0111 : result = 2'b10;
	  4'b1000 : result = 2'b11;
	  4'b1001 : result = 2'b11;
	  4'b1010 : result = 2'b11;
	  4'b1011 : result = 2'b11;
	  4'b1100 : result = 2'b11;
	  4'b1101 : result = 2'b11;
	  4'b1110 : result = 2'b11;
	  4'b1111 : result = 2'b11;	  
	endcase	
     end
endmodule // priority_encoder_4in_case


module priority_encoder_4in_case2
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb
     begin
	valid = 1'b1;
	
	casez (inputs)
	  4'b1??? : result = 2'b11;
	  4'b01?? : result = 2'b10;
	  4'b001? : result = 2'b01;
	  4'b0001 : result = 2'b00;
	  4'b0000 : begin result = 2'b00; valid = 1'b0; end
	endcase	
     end
endmodule // priority_encoder_4in_case2


module priority_encoder_4in
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   priority_encoder_4in_if pe (.*);
   //priority_encoder_4in_case pe (.*);
   //priority_encoder_4in_case2 pe (.*);
endmodule
