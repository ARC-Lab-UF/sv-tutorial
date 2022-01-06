// Greg Stitt
// University of Florida
//
// Description: This file illustrates a gotcha caused by SV allowing illegal
// indexing into unpacked arrays. There is actually a double gotcha in this
// example, because despite there being an obvious error in the code, the
// testbench does not report any errors. See the corresponding testbench for
// an explanation.
//

// Module: mux4x1
// Description: A purposely incorrect 4:1 mux that demonstrates an SV gotcha.
// Although this example is somewhat synthetic, it is repesentative of what
// can easily happen in large designs.

module mux4x1
  #(
    parameter WIDTH=8
    )
   (
    input logic [WIDTH-1:0]  inputs[4],
    input logic [1:0] 	     sel,
    output logic [WIDTH-1:0] out
    );
   
   always_comb begin
      case (sel)
	2'b00 : out = inputs[0];
	2'b01 : out = inputs[1];
	2'b10 : out = inputs[2];
	
	// Here we make a typo to illustrate the problem of using an invalid
	// index into an unpacked array.
	2'b11 : out = inputs[4];
	
	// Surprinsgly, this will compile in Modelsim without any warnings. 
	// Fortunately, Quartus will catch the problem and report an error, but
	// unfortunately the SV standard does not require it to be an error,
	// or even a warning:
	//
	// "If an index expression is out of bounds or if any bit in the index 
	// expression is x or z, then the index shall be invalid. Reading from 
	// an unpacked array of any kind with an invalid index shall return the
	//  value specified in Table 7-1. Writing to an array with an invalid 
	// index shall perform no operation, with the exceptions of writing to 
	// element [$+1] of a queue (described in 7.10.1) and creating a new 
	// element of an associative array (described in 7.8.6). 
	// Implementations may issue a warning if an invalid index occurs for 
	// a read or write operation on an array."
	//
	// So, the standard recommends a warning, but that's it. The only
	// required behavior is for the compiler to return a default value
	// when reading from an invalid index. Similarly, writing to an array
	// with an invalid index simply gets ignored in most cases.
	//
	// For more details, here is an excellent analysis on this gotcha:
	//
	// https://www.amiq.com/consulting/2016/01/26/gotcha-access-an-out-of-bounds-index-for-a-systemverilog-fixed-size-array/
            	
      endcase
   end   
endmodule
