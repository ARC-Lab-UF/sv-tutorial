module add
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    input logic 	     carry_in,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   assign {carry_out, sum} = in0 + in1 + carry_in;
   
endmodule
