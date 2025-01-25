module ff (
    input  logic clk,
    input  logic rst,
    input  logic en,
    input  logic in,
    output logic out
);
    always_ff @(posedge clk or posedge rst)
        if (rst) out <= 1'b0;
        else if (en) out <= in;
endmodule
