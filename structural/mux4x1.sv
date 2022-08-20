// Greg Stitt
// University of Florida
//
// This file illustrates how to create a basic structural architecture by
// combining three 2x1 muxes to create a 4x1 mux.
//
// For any structural architecture, the most critical first step is to draw
// out a schematic of the architecture in terms of modules that have already
// been defined. The structural description is then simply a text representation
// of that schematic.
//
// See mux4x1.pdf for the corresponding schematic.


// Module: mux2x1
// Description: A basic 2x1 mux. We'll be using this to create a structural
// 4x1 mux.

module mux2x1
  (
   input logic  in0,
   input logic  in1,
   input logic  sel,
   output logic out
   );

   assign out = sel == 1'b1 ? in1 : in0;

endmodule // mux2x1


// Module: mux4x1
// Description: A structural implementation of a 4x1 mux using 3 separate 2x1
// muxes. See mux4x1.pdf for a schematic of the architecture.

module mux4x1  
  (
   input logic [3:0] inputs,
   input logic [1:0] sel,
   output logic      out
   );

   // Create internal signals for the connections between modules. Technically
   // this isn't needed because any signal that appears in an instantiation
   // will be automatically delcared with a width of 1 bit. However, I
   // strongly recommend against relying on that functionality and instead
   // just declare all signals. See the gotchas section to see why this can
   // be so problematic.
   logic             mux1_out, mux2_out;
   
   // Instantiate the three muxes from the schematic and connect them together
   // as shown in schematic.
   //
   // Grammar description:
   // The first word is the name of the module being instantianted (mux2x1)
   // The second word is a label for the particular instance. I chose labels
   // that match the schematic, but you can choose any meaningful name.
   // The list in parantheses is the list of I/O connections.
   //
   // The I/O connections can be specified by order, or by name. Order is not 
   // recommended because that order might change, or it might be easy to mess 
   // up the order for large amounts of I/O.
   //
   // Specifying ports by name is less concise, but much less error prone.
   // The name of the port for the module is specified with a . prefix.
   // The name of the signal connected to the port is specified in parantheses.
   // Ports can be left open with empty parantheses.
   //
   // IMPORTANT: if the port name matches the signal name, you can use a
   // wildcard to automatically establish connections. e.g. .*
   // This isn't used for this example, but is incredibly useful in general.
   
   mux2x1 MUX1 (.in1(inputs[3]), .in0(inputs[2]), .sel(sel[0]), .out(mux1_out));
   mux2x1 MUX2 (.in1(inputs[1]), .in0(inputs[0]), .sel(sel[0]), .out(mux2_out));
   mux2x1 MUX3 (.in1(mux1_out), .in0(mux2_out), .sel(sel[1]), .out(out));      
endmodule

