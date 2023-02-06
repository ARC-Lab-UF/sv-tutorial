module mult1
#(parameter int INPUT_WIDTH = 16,
  parameter logic IS_SIGNED = 1'b0)
(
    input logic [INPUT_WIDTH-1:0] in0, in1;
    output logic [2*INPUT_WIDTH-1:0] product;
    // whenever we are multiplying two numbers, 
    // to not loose any bits in the result, we make the width of the 
    // result twice the width of the input.
); 
// By defaul in SV, things are treated as unsigned
// unless explicitly declared as signed.
always_comb begin
    if(IS_SIGNED)
        product = signed'(in0) * signed'(in1);
    else
        product = in0 * in1;
end
endmodule


module mult2
#(
    parameter int INPUT_WIDTH = 16,
    parameter logic IS_SIGNED = 1'b0
    )
    (
    input logic [INPUT_WIDTH-1:0] in0, in1;
    output logic [INPUT_WIDTH-1:0] high, low;
    );
always_block begin
    if(IS_SIGNED)
        {high, low} = signed'(in0) * signed'(in1);
    else begin
        {high, low} = in0 * in1;
        end
    end
endmodule