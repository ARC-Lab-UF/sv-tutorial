module fifo
  #(
    parameter WIDTH=8,
    parameter DEPTH=32
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    output logic 	     full,
    input logic 	     wr_en,
    input logic [WIDTH-1:0]  wr_data,
    output logic 	     empty, 
    input logic 	     rd_en,
    output logic [WIDTH-1:0] rd_data  
    );

   logic [WIDTH-1:0] 	     ram[DEPTH];
   logic [$clog2(DEPTH)-1:0] wr_addr, rd_addr;
   logic [$clog2(DEPTH):0]   count;
   logic 		     valid_wr, valid_rd;
   
   always_ff @(posedge clk, posedge rst) begin
      if (rst) begin
	 rd_addr = '0;
	 wr_addr = '0;
	 count = '0;	 
      end
      else begin
	 if (valid_wr) begin
	    ram[wr_addr] = wr_data;
	    wr_addr ++;
	    count ++;	    
	 end

	 if (valid_rd) begin
	    rd_addr ++;
	    count --;
	 end	   
      end
   end // always_ff @

   assign rd_data = ram[rd_addr];   
   assign valid_wr = wr_en && !full;
   assign valid_rd = rd_en && !empty;
   assign full = count == DEPTH;
   assign empty = count == 0;
    
endmodule
