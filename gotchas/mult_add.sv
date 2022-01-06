// Greg Stitt
// University of Florida

// This file demonstrates a common SV gotcha related to implicit net
// declarations.


// Module: mult
// Description: A basic multiplier.

module mult
  #(parameter WIDTH)
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [2*WIDTH-1:0] product
    );

   assign product = in0 * in1;      
endmodule 


// Module: mult_add_bad
// Description: This module multiplies two pairs of inputs, then sums the 
// result. However, it does not work because of a common implicit net gotcha.
// Even worse, Modelsim gives no warnings for this problem. Most synthesis
// tools will probably give a warning, but synthesis tools often output 1000s
// of harmless warnings, which make it nearly impossible to find actual
// warnings. Basically, with SV you can't rely on the simulator or synthesis
// tool to identifiy this problem.

module mult_add_bad
  #(parameter WIDTH)
  (
   input logic [WIDTH-1:0]  inputs[4],
   output logic [2*WIDTH-1:0] result
   );

   // GOTCHA: mult1_out and mult2_out are never explicitly declared. In this
   // situation, SV will automatically create a 1-bit net. Despite the product
   // being WIDTH*2 bits, SV will automatically truncate the product to a
   // single bit.
   mult #(.WIDTH(WIDTH)) mult1 (.in0(inputs[0]),
				.in1(inputs[1]), 
				.product(mult1_out));
   
   mult #(.WIDTH(WIDTH)) mult2 (.in0(inputs[2]), 
				.in1(inputs[3]), 
				.product(mult2_out));

   // Because mult1/2_out are only bit, but result is WIDTH bits, this line
   // will automitcally resize mult1/2_out to WIDTH bits for the addition.
   // However, since they were originally only 1 bit, the only possible values
   // for result are 0, 1, and 2.
   assign result = mult1_out + mult2_out;
   
endmodule // mult_add_bad


// One possible solution for avoiding implicit net declarations is using the
// following directive, which disables implicit declarations.
// Try uncommenting the mult_add_bad2 module and you should get compiler errors
// for same code.

`default_nettype none // Disable implicit net declarations
/*
  module mult_add_bad2
    #(parameter WIDTH)
   (
    input logic [WIDTH-1:0]    inputs[4],
    output logic [2*WIDTH-1:0] result
    );
   
   mult #(.WIDTH(WIDTH)) mult1 (.in0(inputs[0]),
				.in1(inputs[1]), 
				.product(mult1_out));
   
   mult #(.WIDTH(WIDTH)) mult2 (.in0(inputs[2]), 
				.in1(inputs[3]), 
				.product(mult2_out));
   
   assign result = mult1_out + mult2_out; 
endmodule // mult_add_bad2
*/
  
// If we disable implicit net declarations for a module, we need to renable
// them after the module because there might be some module that uses them.
// This directive basically makes an implicit net have a wire type.
`default_nettype wire // Renable implicit net declarations


// Module: mult_add_good
// Description: This module fixes the implicit net problem by declaring
// internal variables for mult1/2_out.
  
module mult_add_good
  #(parameter WIDTH)
  (
   input logic [WIDTH-1:0]  inputs[4],
   output logic [2*WIDTH-1:0] result
   );

   logic [2*WIDTH-1:0] 	      mult1_out, mult2_out;
   
   mult #(.WIDTH(WIDTH)) mult1 (.in0(inputs[0]),
				.in1(inputs[1]), 
				.product(mult1_out));
   
   mult #(.WIDTH(WIDTH)) mult2 (.in0(inputs[2]), 
				.in1(inputs[3]), 
				.product(mult2_out));

   assign result = mult1_out + mult2_out;
  
endmodule // mult_add_good


module mult_add
   #(parameter WIDTH=8)
  (
   input logic [WIDTH-1:0]  inputs[4],
   output logic [2*WIDTH-1:0] result
   );

   mult_add_bad #(.WIDTH(WIDTH)) top (.*);
      
endmodule // mult_add

