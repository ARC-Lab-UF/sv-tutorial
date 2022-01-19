// Greg Stitt
// University of Florida

// This file shows how to implement an ALU, and how to avoid latches, which are
// a common problem with combinational logic descriptions in HDL.
//
// The ALU has a parameter for width and performs addition (sel = 2'b00),
// subtraction (sel=2'b01), and (sel=2'b10), or (sel=2'b11). There are also
// status flags to signify positive, negative, and zero results.
// For illustrative purposes, assume the flags can be set to any value for
// the "and" and "or" cases.


// Module: alu_bad
// Description:
//
// Although this module  will simulate correctly, there is a synthesis
// problem. Note that the status flags are not defined by the "and" or "or"
// cases, which is ok because we originally defined the flags as meaningless
// for these operations. However, we are describing combinational logic. What
// happens to the flags if the "and" or "or" cases are selected according to
// this code? The answer is that flags must preserve their previous values.
// Using combinational logic, you can't preserve a value, which is the purpose 
// of sequential logic. So, what ends up happening is that the synthesis tool 
// will infer latches. You should avoid it unless you explicitly want to use a 
// latch, which is unlikely.
//
// To solve this problem, every path through the process/block has to define 
// each output from the combinational logic. In this example, the paths 
// through the "and" and "or" cases do not define the flag outputs, and 
// therefore result in latches.
//
// SYNTHESIS GUIDELINE FOR COMBINATIONAL LOGIC: Make sure that every path
// through the block defines every output and internal signal.

module alu_bad
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input logic [1:0] 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );

   always_comb begin

      case (sel)
	// Addition
	2'b00 : begin
	   // Assign the output
	   out = in0 + in1;

	   // Update the status flags
	   if (out == 0) begin
	      pos = 1'b0;
	      neg = 1'b0;
	      zero = 1'b1;
	   end
	   else if (out[WIDTH-1] == 1'b0) begin
	      pos = 1'b1;
	      neg = 1'b0;
	      zero = 1'b0;
	   end
	   else begin
	      pos = 1'b0;
	      neg = 1'b1;
	      zero = 1'b0;
	   end
	end

	// Subtraction
	2'b01 : begin
	   out = in0 - in1;
	   if (out == 0) begin
	      pos = 1'b0;
	      neg = 1'b0;
	      zero = 1'b1;
	   end
	   else if (out[WIDTH-1] == 1'b0) begin
	      pos = 1'b1;
	      neg = 1'b0;
	      zero = 1'b0;
	   end
	   else begin
	      pos = 1'b0;
	      neg = 1'b1;
	      zero = 1'b0;
	   end
	end

	// And
	// We don't assign the status flags here, which is a common mistake
	// because we defined the ALU as having don't care outputs for status
	// flags on and and or. The confusion is mistaking don't care outputs
	// as not having to assign the outputs. This code doesn't specify
	// don't cares. It specifies that the status flags shouldn't change
	// because we aren't assigning them. The only way to preserve their
	// values is by introducing latches, which we don't want with
	// combinational logic.
	2'b10 : begin
	   out = in0 & in1;
	end

	// Or
	2'b11 : begin
	   out = in0 | in1;
	end	   
      endcase      
   end   
endmodule // alu_bad


// Module: alu1
// Description: This module eliminates the latches from the previous module
// by making sure the status flags are assigned on all paths through the block.

module alu1
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input logic [1:0] 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );

   always_comb begin
      case (sel)
	// Addition
	2'b00 : out = in0 + in1;
	// Subtraction
	2'b01 : out = in0 - in1;
	// And
	2'b10 : out = in0 & in1;
	// Or
	2'b11 : out = in0 | in1;   
      endcase

      // By moving the flag definitions outside the case statements, we
      // guarantee that all flags are defined on all paths, which eliminates
      // the latches.
      if (out == 0) begin
	 pos = 1'b0;
	 neg = 1'b0;
	 zero = 1'b1;
      end
      else if (out[WIDTH-1] == 1'b0) begin
	 pos = 1'b1;
	 neg = 1'b0;
	 zero = 1'b0;
      end
      else begin
	 pos = 1'b0;
	 neg = 1'b1;
	 zero = 1'b0;
      end
   end   
endmodule


// Module: alu2
// Description: A slightly simpler implementation of alu1.

module alu2
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input logic [1:0] 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );

   always_comb begin

      // Use default values to simplify code and avoid latches.
      pos = 1'b0;
      neg = 1'b0;
      zero = 1'b0;
      
      case (sel)
	// Addition
	2'b00 : out = in0 + in1;
	// Subtraction
	2'b01 : out = in0 - in1;
	// And
	2'b10 : out = in0 & in1;
	// Or
	2'b11 : out = in0 | in1;   
      endcase
      
      // The default values provided above simplify this code.
      if (out == 0) zero = 1'b1;
      else if (out[WIDTH-1] == 1'b0) pos = 1'b1;
      else neg = 1'b1;
   end   
endmodule


// Module: alu3
// Description: An alternative implementation that demonstrates localparam,
// don't cares, and tasks.

module alu3
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input logic [1:0] 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );

   // We can define constants with meaningful names to replace hardcoded values.
   localparam logic [1:0]    ADD_SEL = 2'b00;
   localparam logic [1:0]    SUB_SEL = 2'b01;
   localparam logic [1:0]    AND_SEL = 2'b10;
   localparam logic [1:0]    OR_SEL = 2'b11;

   // For operations that are common in multiple paths, we can use a task or
   // function to reduce the amount of repeated code. This task updates all
   // status flags based on the output.
   task update_flags();
      pos = 1'b0;
      neg = 1'b0;
      zero = 1'b0;
      if (out == 0) zero = 1'b1;
      else if (out[WIDTH-1] == 1'b0) pos = 1'b1;
      else neg = 1'b1;
   endtask
   
   always_comb begin
      // If we really don't care what values are assigned to the status flags
      // for operations where the flags aren't defined, we can explicitly
      // assign don't care values to potentially help synthesis simplify logic
      // Note that explicit don't cares can cause problems in some tools and
      // can cause warnings in simulations, so use them with caution.
      neg = 1'bx;
      pos = 1'bx;
      zero = 1'bx;
      
      case (sel)
	ADD_SEL : begin 
	   out = in0 + in1;
	   update_flags();	   
	end
	SUB_SEL : begin 
	   out = in0 - in1;
	   update_flags();	   
	end
	AND_SEL : out = in0 & in1;
	OR_SEL : out = in0 | in1;   
      endcase
   end   
endmodule


// Module: alu4
// Description: This version uses a separate package (see alu_pkg.sv) to
// define a custom enum type for the select. This allows us to see meaningful
// select names in simulation.
   
import alu_pkg::*;
     
module alu4
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input alu_sel_t 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );
   
   task update_flags();
      pos = 1'b0;
      neg = 1'b0;
      zero = 1'b0;
      if (out == 0) zero = 1'b1;
      else if (out[WIDTH-1] == 1'b0) pos = 1'b1;
      else neg = 1'b1;
   endtask
   
   always_comb begin
      neg = 1'b0;
      pos = 1'b0;
      zero = 1'b0;
      
      case (sel)
	ADD_SEL : begin 
	   out = in0 + in1;
	   update_flags();	   
	end
	SUB_SEL : begin 
	   out = in0 - in1;
	   update_flags();	   
	end
	AND_SEL : out = in0 & in1;
	OR_SEL : out = in0 | in1;   
      endcase
   end   
endmodule


// Module: alu5
// Description: Nearly identical to the previous module, except this version
// uses the scope resolution operator (::) to specify where the constants
// come from. This can be useful for readability, but is sometimes necessary
// when multiple packages have the same name for constants, functions, etc.
// This issue is known as "namespace" collision." In these cases, we can
// resolve the collision with explicit scope resolution.   

import alu_pkg::*;

module alu5
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input alu_sel_t 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );
   
   task update_flags();
      pos = 1'b0;
      neg = 1'b0;
      zero = 1'b0;
      if (out == 0) zero = 1'b1;
      else if (out[WIDTH-1] == 1'b0) pos = 1'b1;
      else neg = 1'b1;
   endtask
   
   always_comb begin
      neg = 1'b0;
      pos = 1'b0;
      zero = 1'b0;
      
      case (sel)
	alu_pkg::ADD_SEL : begin 
	   out = in0 + in1;
	   update_flags();	   
	end
	alu_pkg::SUB_SEL : begin 
	   out = in0 - in1;
	   update_flags();	   
	end
	alu_pkg::AND_SEL : out = in0 & in1;
	alu_pkg::OR_SEL : out = in0 | in1;   
      endcase
   end   
endmodule


// Module: alu
// Description: top-level module for testing synthesis of each alu module.
   //    
module alu
  #(
    parameter WIDTH=8
    )
   (
    input logic [WIDTH-1:0]  in0,
    input logic [WIDTH-1:0]  in1,
    input logic [1:0] 	     sel,
    output logic 	     neg,
    output logic 	     pos,
    output logic 	     zero, 
    output logic [WIDTH-1:0] out
    );

   
   //alu_bad #(.WIDTH(WIDTH)) alu (.*);
   //alu1 #(.WIDTH(WIDTH)) alu (.*);
   //alu2 #(.WIDTH(WIDTH)) alu (.*);
   //alu3 #(.WIDTH(WIDTH)) alu (.*);

   //alu4 #(.WIDTH(WIDTH)) alu (.sel(alu_sel_t'(sel)), .*);
   alu5 #(.WIDTH(WIDTH)) alu (.sel(alu_sel_t'(sel)), .*);
   
endmodule
