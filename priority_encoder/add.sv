module add
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum
    );

   assign sum = in0 + in1;
   
endmodule


module add_carry_out_bad
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   logic [WIDTH:0] 	     full_sum;   
   
   always_comb begin
      full_sum <= {1'b0,in0} + in1;     
      sum <= full_sum[WIDTH-1:0];
      carry_out <= full_sum[WIDTH];      
   end
   
endmodule


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
   
   always_comb begin
      full_sum = {1'b0,in0} + in1;     
      sum = full_sum[WIDTH-1:0];
      carry_out = full_sum[WIDTH];      
   end
   
endmodule // add_carry_out1

module add_carry_out2
  #(
    parameter WIDTH = 16
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   assign {carry_out, sum} = in0 + in1;
   
endmodule


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

   assign {carry_out, sum} = in0 + in1 + carry_in;
   
endmodule

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

   assign {carry_out, sum} = {1'b0, in0} + in1 + carry_in;

   // Signed overflow occurs if both inputs have the same sign and the output
   // has a different sign.
   assign overflow = (in0[WIDTH-1] == in1[WIDTH-1]) && carry_out != in0[WIDTH-1];
      
endmodule



