// Greg Stitt
// University of Florida

// Module: add
// Description: A basic adder with a parameter for the width of the inputs,
//              which generates a sum of the same width.
module add
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum
    );

   assign sum = in0 + in1;
   
endmodule


// Module: add_carry_out_bad
// Description: An extension of the previous adder to provide a carry out,
//              but done in a way that will not simulate correctly.

module add_carry_out_bad
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   // Use an internal variable to store the WIDTH+1 bit sum, which will be
   // sliced to form the sum and carry out.
   logic [WIDTH:0] 	     full_sum;   
   
   always_comb begin 
      // This incorrect code uses a non-blocking assignment to full_sum,
      // which is only updated at the end of the always block. Non-blocking
      // assignments cause subsequent accesses to the variable to use the
      // previous value. When simulated, sum and carry_out will reflect the
      // inputs from the previous inputs, not the current inputs.
      //
      // VHDL COMPARISON: non-blocking assignments are similar to signal
      // assignments, and block assignments are similar to variable assignments.
      // One nice feature of SV (or Verilog) is that you don't need to declare
      // things differently. Everything is a variable and you can choose
      // different assignments in different contexts.

      // In this example, we also illustrate the concatenation operator, where
      // we extend each input by 1 bit to give use WIDTH+1 bits. As we will
      // see later, this is actually not necessary.
      full_sum <= {1'b0, in0} + {1'b0, in1};     
      sum <= full_sum[WIDTH-1:0];
      carry_out <= full_sum[WIDTH];
   end
   
endmodule // add_carry_out_bad


// Module: add_carry_out1
// Description: A corrected version of the previous adder with carry out.

module add_carry_out1
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   logic [WIDTH:0] 	     full_sum;

   // The corrected version using blocking assignments, causing the accesses
   // to full_sum to use the newly updated value.
   //
   // SYNTHESIS CODING GUIDELINE 2 FOR COMBINATIONAL LOGIC:
   // Only use blocking assignments for combinational logic.
   always_comb begin
      full_sum = {1'b0, in0} + {1'b0, in1};     
      sum = full_sum[WIDTH-1:0];
      carry_out = full_sum[WIDTH];      
   end
   
endmodule // add_carry_out1


// Module: add_carry_out2
// Description: An simplified version of the previous module.

module add_carry_out2
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   // Instead of declaring a separate wider variable and then slicing into it,
   // we can instead use the concantenation operator on the LHS of the
   // assignment. SV chooses the width of an operation based on the max of the
   // operand widths AND the result width. Since the result is 1 bit wider,
   // SV will automatically 0 extend the operands to match. We could have
   // similarly remove the manual concatenations from the previous modules.
   assign {carry_out, sum} = in0 + in1;
   
endmodule


// Module: add_carry_inout
// Description: An extended version of the previous adder that also has a
//              carry in.

module add_carry_inout
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    input logic 	     carry_in,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   // The carry in is automatically extended to match the result width, so
   // we only need to add it to the previous version.
   assign {carry_out, sum} = in0 + in1 + carry_in;
   
endmodule


// Module: add_carry_inout_overflow
// Description: An extension of the previous adder to add a signed overflow.
// Note that overflow is avoided if the carry bit is preserved. However, in
// contexts where the adder is used with other operations that are WIDTH bits,
// the overflow output can be useful to detect signed overflow. It has no
// useful meaning for unsigned arithmetic, in which case carry should be
// checked.

module add_carry_inout_overflow
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    input logic 	     carry_in,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out, overflow
    );

   assign {carry_out, sum} = in0 + in1 + carry_in;

   // Signed overflow occurs if both inputs have the same sign and the output
   // has a different sign. Alternatively, we could xor the two highest carry
   // bits, but in this case we only have access to the carry out, so we use
   // this other equation. For a ripple carry adder, xoring the carries could
   // reduce resources because it is a function with 2 inputs instead of 3.
   assign overflow = (in0[WIDTH-1] == in1[WIDTH-1]) && (carry_out != in0[WIDTH-1]);
      
endmodule



