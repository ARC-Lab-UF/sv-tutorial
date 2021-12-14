// Greg Stitt
// University of Florida

// Modue: mult_top
// Description: Simple top-level design that allows synthesis of each of the
// different multiplier modules from mult.sv.

module mult_top
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );
      
   mult #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) MULT (.*);
   //mult2 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) MULT (.*);

   //logic [INPUT_WIDTH-1:0] 	     high, low;
   //mult_high_low #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) MULT (.*);
   //mult_high_low2 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) MULT (.*);
   //assign product = {high, low};
 
endmodule // mult_top

