// Greg Stitt
// University of Florida

// Module: priority_encoder_4in_if
// Description: implements a 4 input (2 output) priority encoder using an if
// statement, with a valid output that is asserted when any of the inputs are
// asserted.

module priority_encoder_4in_if
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb begin
      // By default, assert valid. For all input combinations but 1, valid is
      // asserted, so this saves some code.
      valid = 1'b1;

      // Use an if statement to encode the priority.
      if (inputs[3] == 1'b1)
	result = 2'b11;
      else if (inputs[2] == 1'b1)
	result = 2'b10;
      else if (inputs[1] == 1'b1)
	result = 2'b01;
      else if (inputs[0] == 1'b1)
	result = 2'b00;
      else begin
	 valid = 1'b0;
	 result = 2'b00;
      end
      
   end
endmodule // priority_encoder_4in_if


// Module: priority_encoder_4in_case
// Description: An alternative implementation that uses a case statement.

module priority_encoder_4in_case1
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb begin
      valid = 1'b1;

      // A case statement doesn't have a natural notion of priority, so we
      // need to define outputs for all input combinations.
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


// Module: priority_encoder_4in_case2
// Description: A slightly simplified implementation with a case statement.

module priority_encoder_4in_case2
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb begin
      valid = 1'b1;

      // Here we combine multiple cases to slightly simply the description.
      case (inputs)      
	4'b0000 : begin result = 2'b00; valid = 1'b0; end
	4'b0001 : result = 2'b00;
	4'b0010, 4'b0011 : result = 2'b01;
	4'b0100, 4'b0101, 4'b0110, 4'b0111 : result = 2'b10;
	4'b1000, 4'b1001, 4'b1010, 4'b1011,
          4'b1100, 4'b1101, 4'b1110, 4'b1111 : result = 2'b11;
      endcase	
   end
endmodule // priority_encoder_4in_case2


// Module: priority_encoder_4in_case3
// Description: A greatly simplified implementation with a case statement.

module priority_encoder_4in_case3
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb begin
      valid = 1'b1;

      // By using "case inside," we can specify ranges of values for each case.
      case (inputs) inside     
	4'b0000 : begin result = 2'b00; valid = 1'b0; end
	4'b0001 : result = 2'b00;
	[4'b0010:4'b0011] : result = 2'b01;
	[4'b0100:4'b0111] : result = 2'b10;
	[4'b1000:4'b1111] : result = 2'b11;
      endcase	
   end
endmodule // priority_encoder_4in_case3


// Module: priority_encoder_4in_case4
// Description: A simplified case statement implementation using wildcards.

module priority_encoder_4in_case4
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   always_comb     begin
      valid = 1'b1;

      // The casez statement allows for wildcard (i.e. don't care) inputs by
      // using a ?
      casez (inputs)
	4'b1??? : result = 2'b11;
	4'b01?? : result = 2'b10;
	4'b001? : result = 2'b01;
	4'b0001 : result = 2'b00;
	4'b0000 : begin result = 2'b00; valid = 1'b0; end
      endcase	
   end
endmodule // priority_encoder_4in_case4


// Module: priority_encoder_4in
// Description: A top-level module that can be used to change the module used
// for synthesis and simulation.

module priority_encoder_4in
  (
   input logic [3:0]  inputs,
   output logic       valid,
   output logic [1:0] result
   );

   // Uncomment the desired module for synthesis.
   priority_encoder_4in_if pe (.*);
   //priority_encoder_4in_case1 pe (.*);
   //priority_encoder_4in_case2 pe (.*);
   //priority_encoder_4in_case3 pe (.*);
   //priority_encoder_4in_case4 pe (.*);
endmodule
