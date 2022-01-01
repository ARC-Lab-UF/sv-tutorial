// Greg Stitt
// University of Florida

// This example demonstrates how synthesis tools convert sequential logic
// descriptions into a circuit. There is one rule that is critically important
// to remember:
//
// If you use a non-blocking assignment for a variable (which also includes 
// outputs) on a rising clock edge, the synthesis tool will infer a register.
//
// Blocking assignments may or may not become registers depending on the usage,
// which is illustrated in the examples.
//
// It is common to accidentally introduce registers by assigning variables on a
// rising clock. Always keep in mind exactly how many registers you want. If
// you have to assign a variable and you don't want it to become a register, 
// you have to assign it outside of the block used for sequential logic,
// or you have to very carefully use a blocking assignment. However, it is much
// safer to use non-blocking assignments until you have a strong understanding
// of the corner cases.
//
// To get rid of unintended registers, do not simply move an assignment outside
// the rising clock else in the same block. This is a violation of my synthesis
// coding guidelines for sequential logic.
//
// If you don't want a register on a particular assignment, that means that 
// the assignment corresponds to an output of combinational logic. You should 
// therefore move the assignment outside a block, or into a separate 
// block that follows my guidelines for combinational logic. 

// INSTRUCTIONS: Please see architectures.pdf for the corresponding schematic
// of each of the following architectures. Use the seq_example module at the
// bottom of the file to synthesize each architecture separately, so you can 
// confirm the synthesized circuit matches the circuit in the pdf.


// Module: arch1
// Implemenation of the arch1 architecture from architectures.pdf

module arch1
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 // Assume that all registers should be reset to 0
	 // There are good reasons to not reset a register (e.g. it reduces fan
	 // out, which can improve clock frequency), but when starting,
	 // it is usually safest to reset all registers. 
	 out1 <= '0;
	 out2 <= '0;
      end
      else begin
	 // A non-block assignment of a variable on a rising clock edge
	 // will always create a register, so this one line of code will 
	 // instantiate the adder and regsiter for out1.
	 // SYNTHESIS RULE: LHS is the register output, RHS is the input.
	 out1 <= in1 + in2;

	 // Creates the second register for out2 and connect it to in3.
	 out2 <= in3;	 
      end      
   end
endmodule // arch1


// Module: arch2
// Implemenation of the arch2 architecture from architectures.pdf

module arch2
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   // Need internal variables for input registers. A variable is not needed for
   // the in3 register for reasons explained below.
   // NOTE: A common naming convention for registers is a _r suffix. I do not
   // appliy this convention to module outputs though.
   logic [WIDTH-1:0] 	     in1_r, in2_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 out1 <= '0;
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;	 
      end
      else begin
	 // Create the two input registers. A separate register is not needed
	 // for in3 because we assign it directly to out2, which creates a
	 // register.
	 in1_r <= in1;
	 in2_r <= in2;

	 // The rest of the circuit is the same, but with the input registers
	 // providing input to the adder.
	 out1 <= in1_r + in2_r;

	 // This creates the register for out2/in3.
	 out2 <= in3;

	 // Note that the order of these statements (despite being
         // sequential statements) does not affect the functionality or the
         // synthesized circuit. It is important to remember that non-blocking
	 // assignments are only updated at the end of the block, so the 
	 // addition operation will always use the previous value of in1_r and
         // in2_r regardless of the ordering of statements. In fact, this
         // behavior matches the one-cycle delay introduced by the two input
         // registers, which is exactly what we want.
      end      
   end
endmodule // arch2


// Module: arch3
// Implemenation of the arch3 architecture from architectures.pdf

module arch3
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   // Here we add a variable for in3_3 since it no longer connects directly to
   // the output register.
   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r;

   // Internal variables for the registers on the output of the first adder.
   logic [WIDTH-1:0]	     add_out1_r, add_out2_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 // Note that we no longer initialize out1 and out2 here because they
	 // no longer correspond to registers.

	 // Reset all the registers.
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
	 add_out1_r <= '0;
	 add_out2_r <= '0;	 
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 // Create the new register for in3.
	 in3_r <= in3;

	 // The add operation from the previous architecture is now stored
         // in register add_out1_r. 
	 add_out1_r <= in1_r + in2_r;
	 add_out2_r <= add_out1_r;	 
      end      
   end // always_ff @

   // To avoid creating an additional register for out1, we assign out1 outside
   // the always block instead of on the rising clock edge. 
   assign out1 = add_out1_r;

   // Similarly, we assign out2 outside on the rising clock edge.
   assign out2 = add_out2_r + in3_r;

   // The combinational logic could have also been done in an always_comb block,
   // but in this simple case there is no benefit to a separate block. However,
   // if the combinational logic becomes complex enough, a separate block
   // becomes beneficial.

   // METHODOLOGY: Note that ultimately what we are doing here is dividing up
   // the circuit into subcircuits where registered outputs of resources are
   // assigned on the rising clock edge, and non-registered outputs of resources
   // (i.e. combinational logic) are assigned outside the rising clock edge and
   // outside the corresponding block.
      
   // COMMON MISTAKE: accidentally assigning out1 and out2 inside the always
   // is very common, which results in a different synthesized circuit. In the
   // best case, this mistake just adds extra registers. However, those extra
   // registers introduce timing delays which very often cause the rest of
   // your circuit to stop working.
   
endmodule // arch3


// Module: arch3_2
// Alternative implemenation of the arch3 architecture from architectures.pdf

module arch3_2
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r;
   logic [WIDTH-1:0]	     add_out2_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
	 out1 <= '0;     
	 add_out2_r <= '0;	 
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;

	 // We can remove add_out1_r by just assigning out1 directly and then
	 // reading from it in the following line. However, this might make it 
	 // harder to see how the code matches the schematic in the pdf.
	 //
	 // VHDL COMPARISON: Older VHDL standards do not allow reading from
	 // outputs, so this strategy would not work.	
	 out1 <= in1_r + in2_r;
	 add_out2_r <= out1;	 
      end      
   end // always_ff @
   
   assign out2 = add_out2_r + in3_r;

endmodule // arch3_2


// Module: arch4_warnings
// Implemenation of the arch4 architecture from architectures.pdf. This
// implementation will generate warnings in some linters and should be avoided.

module arch4_warnings
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   // Note that add_out does not have a _r suffix, because it is not intended
   // to be a register. This convention makes it much easier to visualize
   // the schematic from the code.
   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r, add_out;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 out1 <= '0;
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;	 
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;

	 // By using a blocking assignment, add_out gets its new value before
	 // the next line, which means that the adder and multiplier will be 
	 // connected without a register in between.
	 //
	 // This will synthesize correctly, but could cause warnings because
	 // of a blocking assigning within an always_ff block. Basically, by
	 // adding assignments for combinational logic, we have violated the
	 // intent of always assigning FFs.
	 //
	 // Not all tools will report this warning, so it likely depends on 
	 // your choice of linter and the specific settings.
	 add_out = in1_r + in2_r;	 
	 {out1, out2} <= add_out * in3_r;
      end      
   end // always_ff @

endmodule // arch4_warnings



// Module: arch4
// Implemenation of the arch4 architecture from architectures.pdf.

module arch4
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r, add_out;

   // Changing this from the always_ff to always will eliminate any linter
   // warnings about combinational logic in the always_ff.
   always @(posedge clk or posedge rst) begin
      if (rst) begin
	 out1 <= '0;	 
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;

	 add_out = in1_r + in2_r;
	 {out1, out2} <= add_out * in3_r;
      end      
   end // always_ff @
   
endmodule // arch4


// Module: arch5
// Implemenation of the arch5 architecture from architectures.pdf.

module arch5
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r, add_out;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;
	 
	 add_out = in1_r + in2_r;
	 out2 <= add_out * in3_r;
      end      
   end // always_ff @

   // Despite add_out being a blocking assignment, which by itself leads to
   // combinational logic, the following assignment requires that value to be   
   // preservered, which requires a register. However, that register is not
   // placed between the adder and the multiplier, so the functionality is still
   // correct.
   //
   // SYNTHESIS RULE: blocking assignments on a rising clock edge will not
   // create a register only when all uses of the corresponding variable happen
   // after the definition within the same always block. If there are any
   // uses of the variable in the block before the assignment, or outside the
   // block, there will still be a register. The added register will not be
   // placed in between resouces that read the variable on the rising clock edge
   // after the assignment.
   assign out1 = add_out;   
      
endmodule // arch5


// Module: arch6
// Implemenation of the arch6 architecture from architectures.pdf.

module arch6
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r, add_out;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;
	 
	 out2 <= add_out * in3_r;
      end      
   end // always_ff @

   // To eliminate the extra register for out1, we have to move the
   // corresponding adder outside of the rising edge to create combinational
   // logic.
   assign add_out = in1_r + in2_r;   
   assign out1 = add_out;   
      
endmodule // arch6


module arch6_bad
  #(
    parameter WIDTH
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   logic [WIDTH-1:0] 	     in1_r, in2_r, in3_r;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
	 out2 <= '0;
	 in1_r <= '0;
	 in2_r <= '0;
	 in3_r <= '0;
      end
      else begin
	 in1_r <= in1;
	 in2_r <= in2;
	 in3_r <= in3;

	 // Despite looking very similar to the previous examples, this will
	 // create a register despite out1 not be used anywhere outside the 
	 // block within this module. Because out1 is an output, it 
	 // can be used other places, which requires the register.
	 //
	 // SYNTHESIS RULE: any assignment to an output on a rising clock edge
	 // will always create a register.
	 out1 = in1_r + in2_r;
	 out2 <= out1 * in3_r;
      end      
   end // always_ff @

endmodule // arch6_bad


// Module: seq_example
// Description: Top-level module for synthesizing each of the above 
// architectures.

module seq_example
  #(
    parameter WIDTH = 16
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in1, in2, in3,
    output logic [WIDTH-1:0] out1, out2
    );

   // Change the module name to synthesize a different architecture.
   arch1 #(.WIDTH(WIDTH)) arch (.*);
   
endmodule

