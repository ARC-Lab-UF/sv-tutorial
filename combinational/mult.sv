// Greg Stitt
// University of Florida

// Module: mult1
// Description: Implements a multiplier that prevents overflow by producing
// a product that is twice the width of the inputs. It uses a paremeter to
// specify the input width, and whether or not the inputs are signed.

module mult1
  #(
    parameter INPUT_WIDTH,
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
	// The width of the expression is determined automatically as the 
	// maximum width of all operands and the result. Since the product is 
	// twice as wide as the operands, the multiplication will already 
	// match the width of the product by extending the operand widths.
      	product = signed'(in0) * signed'(in1);                
      else
	product = in0 * in1;
      
   end     
endmodule // mult1


// Module: mult2
// Description: An alternative implementation that uses a generate statement
// instead of an always block. This is a brief preview of generate blocks,
// which will be expanded on in the structural tutorial.

module mult2
  #(
    parameter INPUT_WIDTH,
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
   //
   // The generate/endgenerate wrapper is optional according the the language 
   // definition. Any if/for/case using a parameter or localparam should be 
   // automatically detected as a generate block. However, some tools still
   // explicitly require the generate/endgenerate.
   //
   // IMPORTANT: As we will see in later examples, it is often useful to be
   // able to refer to variables, functions, modules instances, etc. within
   // other generate statements. To do this, each if/for/case within a generate
   // requires a label. It is optional in general, but you won't be able to
   // reference things inside the scope of those generates without the label.
   // See the structural architecture tutorial for more examples.
   generate
      if (IS_SIGNED) begin : l_is_signed
	 assign product = signed'(in0) * signed'(in1);                
      end
      else begin : l_is_unsigned
	 assign product = in0 * in1;
      end
   endgenerate  
endmodule


// Module: mult3
// Description: Illustrates case generate block, and hierarchical access of 
// functions within a generate block. Nobody would ever create a multiplier 
// this way, but it is a convenient way of introducing these constructs.

module mult3
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );

   // Here, we can use a single multiply function to handle both signed and
   // unsigned. The prefix l_mult_func. basically states to find a generate
   // block (in this example, but it could also refer to class objects) with
   // the same name. In general, this would be:
   //     <generate_block_name>.<function_name>
   // If the hierarchy was deeper, we could just add more labels separated by
   // periods. You can also access things other than functions. Basically,
   // anything that falls within the generate block can be accessed (e.g.
   // variables, modules, functions).
   assign product = l_mult_func.multiply(in0, in1);

   // We still want the function to behave differently depending on the 
   // signedness. It is overkill for this example, but one way of doing this
   // if with a case (or if) generate block. If we give this block a label, we
   // can access the contents of that block from anywhere in the module.
   // Notice how we now have two different implementations of the multiply
   // function, but only one will exist at compile time because the generate
   // case (or if) can only use parameters, which are known at compile time.
   //
   // There are obviously many other ways of accomplishing this same goal. For
   // example, we could just add an if to the multiply function that selects
   // between signed and unsigned. This new construct becomes more useful as the
   // different function possibilities become more complex. For example, there
   // is a CRC example using different polynomials here:
   //     https://www.systemverilog.io/generate
   //
   // Personally, while I use case and if generates all the time, I have never
   // had a need to hierachically access anything within a generate block for
   // synthesizable code. I'm sure there are situations where hierarchical 
   // access provides a more elegant solution, but I haven't seen a convincing
   // example yet in synthesizable code. However, adding the labels does allow
   // for hierachical access by testbenches, which can be very useful, so my
   // recommendation is to add the labels even if you aren't using them in your
   // synthesizable code.
   generate
      case (IS_SIGNED)
	1'b0: begin: l_mult_func
	   function automatic [INPUT_WIDTH*2-1:0] multiply(input [$bits(in0)-1:0] x, y);
	      
	      return x * y;
	   endfunction
	end
	1'b1: begin: l_mult_func
	     function automatic [INPUT_WIDTH*2-1:0] multiply(input [$bits(in0)-1:0] x, y);
		
		return signed'(x) * signed'(y);
	     endfunction
	end
      endcase
   endgenerate  
endmodule

// Module: mult_high_low1
// Description: An alternative implementation that replaces the INPUT_WIDTH*2
// bit product with a high and low output. This generally isn't needed since
// it is easy to slice into the larger product, but is used to illustrate
// several new constructs.

module mult_high_low1
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]  in0, in1,
    output logic [INPUT_WIDTH-1:0] high, low
    );

   always_comb begin : l_mult
      // Use a tempory variable to store the full product.
      // Variables can have the scope of an always_block, but if you do this,
      // it is a good idea to give the always block a label (e.g. l_mult)
      // otherwise you will have to figure out the automatic name given to it
      // by the simulator.
      logic [INPUT_WIDTH*2-1:0]    product;
      
      if (IS_SIGNED) begin	 
	 product = signed'(in0) * signed'(in1);
      end
      else begin
	 product = in0 * in1;
      end

      // Slice into the product to get the high and low outputs.
      high = product[INPUT_WIDTH*2-1:INPUT_WIDTH];
      low = product[INPUT_WIDTH-1:0];
   end
endmodule


// Module: mult_high_low2
// Description: An alternative implementation that simplifies the previous
// version by using concatenation on the outputs.

module mult_high_low2
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]  in0, in1,
    output logic [INPUT_WIDTH-1:0] high, low
    );

   always_comb begin
      if (IS_SIGNED) begin
	 // Use concatenation on the outputs to avoid the extra variable. This
	 // synthesizes to the exact same circuit, but is more concise.
	 {high,low} = signed'(in0) * signed'(in1);              
      end
      else begin
	 {high,low} = in0 * in1;
      end
   end

endmodule


// Module: mult
// Description: Top level for testing synthesis of each module. Change the
// comments to change the top-level module.

module mult
  #(
    parameter INPUT_WIDTH=16,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );

   //mult1 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) top (.*);
   //mult2 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) top (.*);
   //mult3 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) top (.*);

   //mult_high_low1 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) top (.high(product[2*INPUT_WIDTH-1:INPUT_WIDTH]), .low(product[INPUT_WIDTH-1:0]), .*);
   mult_high_low2 #(.INPUT_WIDTH(INPUT_WIDTH), .IS_SIGNED(IS_SIGNED)) top (.high(product[2*INPUT_WIDTH-1:INPUT_WIDTH]), .low(product[INPUT_WIDTH-1:0]), .*);
   
endmodule
