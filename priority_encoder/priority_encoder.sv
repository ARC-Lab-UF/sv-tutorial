// Greg Stitt
// University of Florida



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
      result = '0;
      valid = 1'b0;     
      
      for (int i=NUM_INPUTS-1; i >= 0; i--) begin
	 if (inputs[i] == 1'b1) begin
	    result = i;
	    valid = 1'b1;
	    break;	    
	 end
      end      
   end   
endmodule // priority_encoder
