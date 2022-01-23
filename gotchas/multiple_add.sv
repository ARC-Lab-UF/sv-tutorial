// Greg Stitt
// University of Florida
//
// In this example, we demonstrate how an input to a module can accidentally be
// driven from inside the module through an incorrect port mapping.

// Module: multiple_add2
// Description: This module simply takes an input, registers it, and adds it
// with NUM_ADDERS separate constants to generate NUM_ADDERS outputs.
// There is nothing wrong with this module, but when we try to synthesize it
// with multiple_add (see below) as the top-level module, we'll see all the
// outputs are disconnected.

module multiple_add2
  #(
    parameter int DATA_WIDTH=32,
    parameter int NUM_ADDERS=64
    )
   (
    input logic 		  clk,
    input logic 		  rst,
    input logic [DATA_WIDTH-1:0]  in,
    output logic [DATA_WIDTH-1:0] out[NUM_ADDERS]
    );

   logic [DATA_WIDTH-1:0] in_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 in_r <= '0;
	 for (int i=0; i < NUM_ADDERS; i++) out[i] <= '0;
      end
      else begin
	 in_r <= in;
	 for (int i=0; i < NUM_ADDERS; i++) out[i] <= in_r + DATA_WIDTH'(i);
      end
   end
endmodule


// Module: multiple_add
// Description: A top-level module illustrating a subtle problem that can
// cause the entire design to be optimized away without errors or warnings.

module multiple_add
  #(
    parameter int DATA_WIDTH=16,
    parameter int NUM_ADDERS=8
    )
   (
    input logic 		 clk,
    input logic 		 rst,
    input logic [DATA_WIDTH-1:0] in,
    // Here we make the mistake of specifying out as an input. Ideally, this
    // would cause an error, but we will see that it doesn't.
    input logic [DATA_WIDTH-1:0] out[NUM_ADDERS]
    );

   // Here we simply instantiate another module with the same parameters and
   // port to do the actual work.
   // What happens here is that the input out from the current module gets
   // connected to the output out from the instanitated module, which doesn't
   // make any sense. I haveen't tested other synthesis tools, but Quartus
   // lets us do this, and then since there aren't any actual outputs, the
   // entire design gets optimized away.
   //
   // GOTCHA: you can accidentally drive an input internally through a port
   // mapping.
   
   multiple_add2 #(.DATA_WIDTH(DATA_WIDTH), .NUM_ADDERS(NUM_ADDERS)) top (.*);

   // We get the same problem if we specify it explicitly.
   //multiple_add2 #(.DATA_WIDTH(DATA_WIDTH), .NUM_ADDERS(NUM_ADDERS)) top (.out(out), .*);

   // Interestingly, if we try to assign something to an input, we get errors,
   // so, the gotcha is when you accidentally port map an output onto an input.
endmodule
