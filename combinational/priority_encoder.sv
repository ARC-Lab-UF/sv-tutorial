// Greg Stitt
// University of Florida

// Module: priority_encoder
// Description: A parameterized priority encoder that supports any number of
// inputs. The module assumes that the MSB of the input is highest priority.

// NOTE: This might not synthesize efficiently in all tools.
// See https://opencores.org/projects/priority_encoder for alternative.

module priority_encoder
  #(
    parameter NUM_INPUTS
    )
   (
    input logic [NUM_INPUTS-1:0] 	  inputs,
    output logic [$clog2(NUM_INPUTS)-1:0] result,
    output logic 			  valid
    );

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
	    result = i;
	    valid = 1'b1;
	    break;	    
	 end
      end      
   end   
endmodule // priority_encoder
