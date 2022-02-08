// Greg Stitt
// University of Florida

// Module: register
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register
  #(
    parameter WIDTH
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
   
endmodule
