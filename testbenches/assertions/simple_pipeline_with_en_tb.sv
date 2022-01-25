// Greg Stitt
// University of Florida
//
// This testbench illustrates how to extend the simple_pipeline testbench
// to include an enable.

`timescale 1 ns / 100 ps

module simple_pipeline_with_en_tb;

   localparam int NUM_TESTS = 10000;
   localparam int WIDTH = 8;
      
   logic 	  clk, rst, en, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, " ns");

      // Reset the circuit.
      rst <= 1'b1;
      en <= 1'b0;      
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      rst <= 1'b0;
      @(posedge clk);

      // Run the tests.      
      for (int i=0; i < NUM_TESTS; i++) begin
	 en <= $random;	 
	 for (int i=0; i < 8; i++) in[i] <= $random;
	 valid_in <= $random;	 
	 @(posedge clk);
      end

      $display("Tests completed.");      
      disable generate_clock;
   end

   // In this example, we use a simpler function that returns the correct
   // output, instead of comparing with the correct output directly. When
   // there is a single output, this strategy is preferred, but when the
   // output is an array, you often need a function to verify all output values.
   function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] in[8]);
      logic [WIDTH-1:0] sum = 0;
      for (int i=0; i < 4; i++) sum += in[i*2] * in[i*2+1];	 
      return sum;     
   endfunction
   
   // This needs to include the enable now because the pipeline only advances 
   // when en is asserted.
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < DUT.LATENCY) count ++;

   // We need to account for stalls, instead of just waiting for the latency.
   // Fortunately, the $past function can be enabled with a third paremeter,
   // for which we use our en signal.
   assert property(@(posedge clk) disable iff (rst) count == DUT.LATENCY |-> model($past(in, DUT.LATENCY, en)) == out);
   
   // Make sure the valid output is not asserted after reset until the pipeline
   // fills up.
   assert property (@(posedge clk) disable iff (rst) count < DUT.LATENCY |-> valid_out == '0);

   // Make sure all pipeline stages are reset.
   assert property (@(posedge clk) disable iff (rst) count < DUT.LATENCY |-> out == '0);
      
endmodule
