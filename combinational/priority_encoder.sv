// Greg Stitt
// University of Florida

// Module: priority_encoder
// Description: A parameterized priority encoder that supports any number of
// inputs. The module assumes that the MSB of the input is highest priority.

// NOTE: These examples might not synthesize efficiently in all tools.
// See https://opencores.org/projects/priority_encoder for alternative.

// Module: priority_encoder1
// Description: Illustrates a for loop and local parameters.

module priority_encoder1
  #(
    parameter NUM_INPUTS
    )
   (
    input logic [NUM_INPUTS-1:0] 	  inputs,
    output logic [$clog2(NUM_INPUTS)-1:0] result,
    output logic 			  valid
    );
   
   // Local parameters are just constants inside the scope of the module.
   localparam NUM_OUTPUTS = $clog2(NUM_INPUTS);
         
   always_comb begin
      // This notation sets all bits to 0. 
      // VHDL COMPARISON: (others => '0')
      result = '0;
      valid = 1'b0;

      // Iterate from the highest input down. After finding the first bit that
      // is asserted, set the result accordingly and exit the loop.
      //
      // IMPORTANT: Keep in mind that synthesis will always fully unroll a for
      // loop and optimize accordingly. 
      for (int i=NUM_INPUTS-1; i >= 0; i--) begin
	 if (inputs[i] == 1'b1) begin

	    // The following is a common technique, but can cause warnings
	    // about width mismatches in some tools. These warnings are good
	    // in my opinion because we are storing a 32-bit integer value
	    // into an array with fewer bits, which requires truncation. While
	    // we might be ok with that truncation here, there will be times
	    // where we do it on accident, which would require extra debugging
	    // during simulation.
	    //
	    // result = i;

	    // To eliminate this warning, I often see people try the following
	    // syntax to match other literals:
	    //
	    // result = NUM_OUTPUTS'i;
	    //
	    // Unfortunately, this doesn't work, even if i is hardcoded.
	    // Fortunately, there is a way of specifying the width of any
	    // expression, which just requires parantheses. So, we can do this
	    // to eliminate any warnings.

	    result = NUM_OUTPUTS'(i);	        	    	    
	    valid = 1'b1;
	    break;	    
	 end
      end      
   end   
endmodule // priority_encoder1


// Module: priority_encoder2
// Description: This module illustrates a slightly different implementation.

module priority_encoder2
  #(
    // Parameters don't require a type, but it is a good design practice. If
    // you don't use a type, they get their type based on the value used when 
    // instantiated. See the following for more details:
    //
    // https://bradpierce.wordpress.com/2015/01/07/a-verilog-parameter-infers-its-type-from-its-value-the-myth-that-there-is-a-default-signed-integer-parameter-type-in-verilog/
    parameter int NUM_INPUTS
    )
   (
    input logic [NUM_INPUTS-1:0] 	  inputs,
    output logic [$clog2(NUM_INPUTS)-1:0] result,
    output logic 			  valid
    );

   // Localpararms also do not require a type, but it is good practice 
   localparam int NUM_OUTPUTS = $clog2(NUM_INPUTS);
      
   always_comb begin
      result = '0;
      valid = 1'b0;

      // Similar code as before, but we start from bit 0. Because we start with
      // the lowest priority bit, we don't break when finding an asserted bit.
      for (int i=0; i < NUM_INPUTS; i++) begin
	 if (inputs[i] == 1'b1) begin
	    result = NUM_OUTPUTS'(i);	        	    	    
	    valid = 1'b1;
	 end
      end      
   end   
endmodule // priority_encoder2


// Module: priority_encoder3
// Description: This version illustrates how to use parameters that are given
// default values based on other parameters.

module priority_encoder3
  #(
    parameter int NUM_INPUTS,

    // SV allows parameters to be given default values in terms of other
    // parameters. We can use this do replace the localparam from the earlier
    // modules. The risk in doing this is that a user could override this
    // default with an incorrect value, but the advantage is we can now define
    // the port using this parameter, whereas before we had to repeat the clog2
    // computation.
    parameter int NUM_OUTPUTS = $clog2(NUM_INPUTS)
    )
   (
    input logic [NUM_INPUTS-1:0]   inputs,

    // Here we use the new parameter to define the width of the result.
    output logic [NUM_OUTPUTS-1:0] result,
    output logic 		   valid
    );
      
   always_comb begin
      result = '0;
      valid = 1'b0;

      for (int i=NUM_INPUTS-1; i >= 0; i--) begin
	 if (inputs[i] == 1'b1) begin
	    result = NUM_OUTPUTS'(i);	        	    	    
	    valid = 1'b1;
	    break;	    
	 end
      end      
   end   
endmodule // priority_encoder3


// Module: priority_encoder
// Description: A top-level module for choosing different implemenetations
// for synthesis.

module priority_encoder
  #(
    parameter int NUM_INPUTS=16,
    parameter int NUM_OUTPUTS = $clog2(NUM_INPUTS)
    )
   (
    input logic [NUM_INPUTS-1:0]   inputs,
    output logic [NUM_OUTPUTS-1:0] result,
    output logic 		   valid
    );

   //priority_encoder1 #(.NUM_INPUTS(NUM_INPUTS)) TOP (.*);
   //priority_encoder2 #(.NUM_INPUTS(NUM_INPUTS)) TOP (.*);
   priority_encoder3 #(.NUM_INPUTS(NUM_INPUTS)) TOP (.*);
   
   
endmodule
