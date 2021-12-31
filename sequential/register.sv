// Greg Stitt
// University of Florida

// Module: register_async_rst
// Description: Implements a register with an active high, asynchronous reset.

module register_async_rst
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );

   // Sequential logic should usually use the always_ff block. For a register
   // or flip flop with an asynchronous reset, we want to update the output
   // on any rising clock edge or reset edge.
   always_ff @(posedge clk or posedge rst) begin
      
      // Checking reset first gives it priority over the clock edge, which is
      // what we want for an asynchronous reset.
      if (rst)
	out <= '0;
      else
	// This else corresponds to anything on a rising clock edge.
	// SYNTHESIS RULE: Any non-blocking assignment on a rising clock edge
	// will synthesize into a register. Blocking assignments can be mixed
	// with non-blocking assignments, but will cause warnings in always_ff
	// blocks because they don't always synthesize to a register.
	out <= in;
   end

   // NOTE: This could have been implemented as:
   //    always @(posedge clk or posedge rst) begin
   // However, always_ff applies additional checks to ensure that everything
   // assigned in the process is synthesized as a flip flop. When mixing
   // sequential logic with combinational logic, a normal always block is more
   // appropriate.

endmodule // register_async_rst


// Module: register_sync_rst
// Description: Implements a register with an active high, synchronous reset.

module register_sync_rst
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );

   // For a synchronous reset, we only want to update outputs a clock edge.
   always_ff @(posedge clk) begin
      // The inside of all the always block is identical, but now the reset is
      // synchronous because this if statement will only ever happen on a clock
      // edge.
      if (rst)
	out <= '0;
      else
	out <= in;
   end
endmodule // register_sync_rst


// Module: register_en_async_rst
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register_en_async_rst
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic 	     en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
	out <= '0;

      // Registers typically have an enable or a load signal which must be
      // asserted for the output to change. We can implement this by simply
      // checking if the enable is asserted on a rising clock edge.
      else if (en)
	out <= in;    	
   end 
   
endmodule // register_en_async_rst


// Module: register
// Description: Implements a parameterized register with a configuration 
// parameters for width, type of reset, reset activation level, and reset value.

module register
  #(
    parameter WIDTH = 16,
    parameter logic HAS_ASYNC_RESET = 1'b1,
    parameter logic RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic 	     en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   // Use generate statements to allow for a fully parameterized register.
   // Generally, this much parameterization for sequential logic becomes
   // cumbersome and error prone because of copying and pasting.
   // When targetting FPGAs, I suggest using asynchronous resets in most cases
   // since they tend to use fewer resources than synchronous resets.
   // For activation levels, one small disadvantage of parameterization is that
   // the name of the reset signal can't specify the activation level (e.g.
   // rst_n vs rst).
   // In addition, another disadvantage of this much parameterization is that it
   // complicates testing and verification. 
   generate      
      if (HAS_ASYNC_RESET) begin	 
	 if (RESET_ACTIVATION_LEVEL) begin
	    // Create an active high async reset.
	    // TODO: See if all synthesis tools support (posedge clk or rst),
	    // which would eliminate the if-else for activation level.
	    always_ff @(posedge clk or posedge rst) begin
	       // Explicitly check the activation level of the reset to support
	       // active high or low.
	       if (rst == RESET_ACTIVATION_LEVEL)
		 // Use the reset value parameter instead of 0.
		 out <= RESET_VALUE;
	       else if (en)
		 out <= in;    	
	    end
	 end
	 else begin
	    // Create an active low async reset.
	    always_ff @(posedge clk or negedge rst) begin
	       if (rst == RESET_ACTIVATION_LEVEL)
		 out <= RESET_VALUE;
	       else if (en)
		 out <= in;    	
	    end
	 end
      end
      else begin
	 // Create an sync reset.
	 always_ff @(posedge clk) begin
	    if (rst == RESET_ACTIVATION_LEVEL)
	      out <= RESET_VALUE;	      
	    else if (en)
	      out <= in;
	 end	
      end
   endgenerate   
endmodule // register

