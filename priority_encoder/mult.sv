// Greg Stitt
// University of Florida

// Module: mult
// Description: Implements a multiplier that prevents overflow by producing
// a product that is twice the width of the inputs. It uses a paremeter to
// specify the input width, and whether or not the inputs are signed.

module mult
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );
   
   always_comb begin
      if (IS_SIGNED) 
	// SV arithmetic operations are unsigned by default, so we have to
	// explicitly cast both inputs to signed.
	// The width of an expression is determined automatically as the 
	// maximum width of all operands and the result. Since the product is 
	// twice as wide as the operands, the multiplication will already 
	// match the width of the product by extending the operand widths.
      	product = signed'(in0) * signed'(in1);                
      else
	product = in0 * in1;
      
   end     
endmodule // mult


// Module: mult2:
// Description: An alternative implementation that uses a generate statement
// instead of an always block.

module mult2
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );

   // In this version of the multiplier, we use generate statements and
   // assign statements to accomplish the same functionality without an
   // always block. The two should synthesize identically since the
   // if condition is a constant, which should be optimized to eliminate the 
   // unused path.
   generate
      if (IS_SIGNED) begin
	 assign product = signed'(in0) * signed'(in1);                
      end
      else begin
	 assign product = in0 * in1;
      end
   endgenerate  
endmodule


// Module: mult_high_low
// Description: An alternative implementation that replaces the INPUT_WIDTH*2
// bit product with a high and low output. This generally isn't needed since
// it is easy to slice into the larger product, but is used to illustrate
// several new constructs.

module mult_high_low
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]  in0, in1,
    output logic [INPUT_WIDTH-1:0] high, low
    );
   
   generate
      // Use a tempory variable to store the full product.
      logic [INPUT_WIDTH*2-1:0]    product;
      if (IS_SIGNED) begin	 
	 always_comb product = signed'(in0) * signed'(in1);
      end
      else begin
	 always_comb product = in0 * in1;
      end

      // Slice into the product to get the high and low outputs.
      assign high = product[INPUT_WIDTH*2-1:INPUT_WIDTH];
      assign low = product[INPUT_WIDTH-1:0];      
      
   endgenerate  
endmodule


// Module: mult_high_low2
// Description: An alternative implementation that simplifies the previous
// version by using concatenation on the outputs.

module mult_high_low2
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]  in0, in1,
    output logic [INPUT_WIDTH-1:0] high, low
    );

   generate
      if (IS_SIGNED) begin
	 // Use concatenation on the outputs to avoid the extra variable. This
	 // synthesizes to the exact same circuit, but is more concise.
	 assign {high,low} = signed'(in0) * signed'(in1);              
      end
      else begin
	 assign {high,low} = in0 * in1;
      end
   endgenerate  
endmodule
