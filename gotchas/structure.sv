// Greg Stitt
// University of Florida
//
// This file demonstrates gotchas related to width mismatches in structural
// architectures.

module add
  #(parameter WIDTH)
   (
    input logic [WIDTH-1:0]  in0, in1,
    output logic [WIDTH-1:0] sum
    );

   assign sum = in0 + in1;      
endmodule // add


// Module: structure
// Description: A synthetic module to demonstrate what happens with width
// mismatches in structure architectures.

module structure
  (
   input logic [31:0] in0, in1,
   output logic [31:0] result1, result2, result3
   );

   logic [15:0]        sum1;
   logic [63:0]        sum2;
   logic [63:0]        sum3;

   // Actual parameters with larger inputs (32 bits -> 16 bits)
   // This simply truncates the inputs, but will likely not give a simulation
   // warning. Synthesis will likely give a warning.
   add #(.WIDTH(16)) add1 (.in0(in0), .in1(in1), .sum(sum1));
   
   // Actual parameters with smaller inputs (32 bits -> 64 bits)
   // In Modelsim, the upper 32 bits of the inputs are Z because they are
   // essentially disconnected. As a result, the sum is undefined. However,
   // synthesis tools report just a warning, so the behavior is going to differ
   // between simulation and synthesis, which is what we want to avoid at all
   // costs.
   add #(.WIDTH(64)) add2 (.in0(in0), .in1(in1), .sum(sum2));
   
   // Actual output parameter with more bits (64 bits -> 32 bits)
   // Unlike when then formal parameter has more bits and the extra bits are
   // disconnected, in this case, the extra bits in the actual parameter are
   // extended.
   add #(.WIDTH(32)) add3 (.in0(in0), .in1(in1), .sum(sum3));

   assign result1 = sum1;
   assign result2 = sum2;
   assign result3 = sum3;   

endmodule


// Module: structure2
// Description: A small modification to the previous module that uses the
// wildcard connections. Interestingly, when you start the simulation, 
// Modelsim reports errors in this case instead of warnings, which in my 
// opinion is the preferred behavior. 
//
// My guess is this is actually defined by the standard, where they are 
// assuming that if you explicitly connect a specific signal, you are aware of 
// the width difference. Similarly, if you are using a wildcare, it is looking 
// for a signal with the exact same name and width. TODO: Confirm this is how 
// the standard defines it.

module structure2
  (
   input logic [31:0] in0, in1,
   output logic [31:0] result1, result2, result3
   );

   logic [15:0]        sum1;
   logic [63:0]        sum2;
   logic [63:0]        sum3;

   add #(.WIDTH(16)) add1 (.sum(sum1), .*);
   add #(.WIDTH(64)) add2 (.sum(sum2), .*);
   add #(.WIDTH(32)) add3 (.sum(sum3), .*);

   assign result1 = sum1;
   assign result2 = sum2;
   assign result3 = sum3;   

endmodule
