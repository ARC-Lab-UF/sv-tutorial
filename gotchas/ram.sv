// Greg Stitt
// University of Florida
//
// TODO: Add testbench to see how Modelsim handles these examples. Also, check
// synthesis results in Quartus to see how the RAM is getting synthesized.

// Module: ram
// Description: This module implements a problematic RAM to demonstrate a
// gotcha with invalid array indexing.

module ram
   (
    input logic 	clk,
    input logic [7:0] 	rd_addr,
    output logic [15:0] rd_data,
    
    input logic 	wr_en,
    input logic [7:0] 	wr_addr,
    input logic [15:0] 	wr_data
    );

   // The problem is that the RAM only has 64 words of storage. However, the
   // addresses are 8 bits, which corresponds to 256 words. Although it is not
   // uncommon for a RAM to not fill up the entire address space of a system, 
   // it would be really strange to purposely create a RAM with fewer words
   // than the address lines would support.
   //
   // Since such an occurrence would almost always be a design error, ideally
   // the compiler would tell us if we tried to access this array outside its
   // bounds.
   logic [15:0] 	ram[64];

   always_ff @(posedge clk) begin
      // GOTCHA: Here we are accessing the ram array using an index that
      // potentially exceeds the ram bounds. However, when we compile, we get
      // no errors. While some tools might report a warning, Quartus did not in
      // our tests.
      //
      // What ends up happening here is that the address is simply truncated to
      // fit within the bounds of the ram array. Although there might be very
      // rare situations where we would want that, the vast majority of the time
      // this would likely be accidental. Since there isn't even a warning, we
      // would have to debug this in simulation in the best case.
      rd_data <= ram[rd_addr];

      // We have a similar issue here. In fact, this could potentially be worse
      // be writes to addresses >= 64 would overwrite data in the RAM, which
      // could be difficult to debug.
      if (wr_en)
	ram[wr_addr] <= wr_data;      
   end
            
endmodule


// Module: ram2
// Description: A similar ram that demonstrates a similar problem where
// the RAM has more words than can be accessed by a corresponding address.
// Like before, Quartus reports no warnings.

module ram2
   (
    input logic 	clk,
    input logic [7:0] 	rd_addr,
    output logic [15:0] rd_data,
    
    input logic 	wr_en,
    input logic [7:0] 	wr_addr,
    input logic [15:0] 	wr_data
    );

   // Here, we make the RAM 1024 words. With an 8-bit address, most of this
   // RAM is inaccessible. However, Quartus reports no warnings. 
   logic [15:0] 	ram[1024];

   always_ff @(posedge clk) begin
      rd_data <= ram[rd_addr];
      if (wr_en)
	ram[wr_addr] <= wr_data;      
   end
            
endmodule
