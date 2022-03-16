// Greg Stitt
// University of Florida
//
// This testbench illustrates how to create a testbench for a simple pipeline
// without an enable. It also demonstrates subtle timing differences when 
// functions are used within assertion properties.
//
// TODO: Change the commented out assertion properties to test each version. 

`timescale 1 ns / 100 ps

module simple_pipeline_tb;

   localparam int NUM_TESTS = 1000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, " ns");

      // Reset the circuit.
      rst <= 1'b1;
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);

      // Run the tests.      
      for (int i=0; i < NUM_TESTS; i++) begin
         for (int i=0; i < 8; i++) in[i] = $random;
         valid_in <= $random;
         @(posedge clk);
      end

      $display("Tests completed.");      
      disable generate_clock;
   end

   // Although this function is a correct reference model for the pipeline,
   // when it is used as part of the assertion properties, it provides incorrect
   // results because the out variable has already been updated with the new
   // output value, but the in input corresponds to the old input.
   function automatic logic is_out_correct1(logic [WIDTH-1:0] in[8]);      
     logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   // To solve the problem with the previous function, we simply add a parameter
   // to the function that takes the output from the assertion property, which
   // ensures that the output has not been changed yet after the clock edge.
   function automatic logic is_out_correct2(logic [WIDTH-1:0] in[8], logic [WIDTH-1:0] out);
      logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   // Track the amount of pipeline stages that are full.
   // After count == DUT.LATENCY, the pipeline is outputting valid data that
   // can be checked for correctness.
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < DUT.LATENCY) count ++;
   
   // This attempt at an assertion property does not work because the function
   // call uses an updated value for out, instead of the value that existed
   // on the clock edge.
   //assert property(@(posedge clk) disable iff (rst) count == DUT.LATENCY |-> is_out_correct1($past(in, DUT.LATENCY)));

   // This version fixes the problem by passing the current value of out to the
   // reference model function. The assertion has access to the current value
   // of out, but if the function tries to access the out variable from outside
   // the assertion, it gets the value that has been updated after the clock.
   assert property(@(posedge clk) disable iff (rst) count == DUT.LATENCY |-> is_out_correct2($past(in, DUT.LATENCY), out));

   // This is an alternate version that also works.
   //assert property(@(posedge clk) disable iff (rst) count < DUT.LATENCY || is_out_correct2($past(in, DUT.LATENCY), out));
   
   // Make sure the valid output is not asserted after reset until the pipeline
   // fills up.
   assert property (@(posedge clk) disable iff (rst) count < DUT.LATENCY |-> valid_out == 1'b0);

   // Make sure valid out is asserted after the pipeline is full.
   assert property (@(posedge clk) disable iff (rst) count == DUT.LATENCY |-> valid_out == $past(valid_in, DUT.LATENCY));
   
   // Make sure all pipeline stages are reset.
   assert property (@(posedge clk) disable iff (rst) count < DUT.LATENCY |-> out == '0);
      
endmodule
