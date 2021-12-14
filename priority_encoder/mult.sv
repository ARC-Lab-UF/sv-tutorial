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
	// explicitly cast both inputs to sign.
	// The width of an expression is determined automatically as the 
	// maximum width of all operands and the result. Since the product is 
	// twice as wide as the operands, the multiplication will already 
	// match the width of the product by extending the operand widths.
      	product = signed'(in0) * signed'(in1);                
      else
	product = in0 * in1;
      
   end     
endmodule // mult


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
   // if condition in the always block is a constant, which would be optimized
   // to eliminate the unused path.
   generate
      if (IS_SIGNED) begin
	 assign product = signed'(in0) * signed'(in1);                
      end
      else begin
	 assign product = in0 * in1;
      end
   endgenerate  
endmodule


module mult3
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]  in0, in1,
    output logic [INPUT_WIDTH-1:0] high, low
    );
  
   generate
      logic [INPUT_WIDTH*2-1:0] product;
      if (IS_SIGNED) begin	 
	 always_comb product = signed'(in0) * signed'(in1);
      end
      else begin
	 always_comb product = in0 * in1;
      end

      assign high = product[INPUT_WIDTH*2-1:INPUT_WIDTH];
      assign low = product[INPUT_WIDTH-1:0];      
            
   endgenerate  
endmodule


module mult4
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
	 assign {high,low} = signed'(in0) * signed'(in1);              
      end
      else begin
	 assign {high,low} = in0 * in1;
      end
   endgenerate  
endmodule
