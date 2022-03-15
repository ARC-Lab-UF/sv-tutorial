// Greg Stitt
// University of Florida
// This file provides a basic FIFO module with a 1-cycle read latency.

module fifo
  #(
    parameter WIDTH,
    parameter DEPTH
    )
   (
    input logic              clk,
    input logic              rst,
    output logic             full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    output logic             empty, 
    input logic              rd_en,
    output logic [WIDTH-1:0] rd_data  
    );

   localparam int READ_LATENCY = 1;
   
   logic [WIDTH-1:0]         ram[DEPTH];
   logic                     valid_wr, valid_rd;

   localparam int            ADDR_WIDTH = $clog2(DEPTH)+1;
   logic [ADDR_WIDTH-1:0]   wr_addr_r, rd_addr_r;

   always_ff @(posedge clk) begin
      if (valid_wr) ram[wr_addr_r[ADDR_WIDTH-2:0]] <= wr_data;
      rd_data <= ram[rd_addr_r[ADDR_WIDTH-2:0]];      
   end
      
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         rd_addr_r <= '0;
         wr_addr_r <= '0;
      end
      else begin         
         if (valid_wr) wr_addr_r <= wr_addr_r + 1'b1;
         if (valid_rd) rd_addr_r <= rd_addr_r + 1'b1;
      end
   end 
      
   assign valid_wr = wr_en && !full;
   assign valid_rd = rd_en && !empty;

   assign full = rd_addr_r[ADDR_WIDTH-2:0] == wr_addr_r[ADDR_WIDTH-2:0] && rd_addr_r[ADDR_WIDTH-1] != wr_addr_r[ADDR_WIDTH-1];

   assign empty = rd_addr_r == wr_addr_r;
      
endmodule
