// Greg Stitt
// University of Florida

`timescale 1 ns / 10 ps

module add_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);
   
   // The adder doesn't have a clock, but we can still use on in the testbench
   // to coordinate assertion and cover properties.
   logic 	     clk;
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin
      logic 	   correct_carry_out;      
      $timeformat(-9, 0, " ns");

      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 correct_carry_out = {{1'b0, in0} + in1 + carry_in}[WIDTH];
	 @(posedge clk);
      end

      $display("Tests completed.");
      disable generate_clock;      
   end

   // These assertions will report errors if there are any incorrect outputs.
   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);

   // However, those assertions don't guarantee that we've tested everything.
   // We could use cover properties to test for certain situations that are
   // likely to cause errors.
   //
   // These make sure there was at least one test where there was a carry in
   // used as input, and at least one test that generated a carry out.
   cp_carry_in : cover property (@(posedge clk) carry_in);
   cp_carry_out : cover property (@(posedge clk) carry_out);

   // Here we check to make sure that both inputs were 0 at some point.
   cp_in0_eq_0 : cover property (@(posedge clk) in0 == 0);
   cp_in1_eq_0 : cover property (@(posedge clk) in1 == 0);

   // Here we check to make sure both inputs are tested with their maximum
   // amounts. To get the maximum amount, we use the replication operator.
   cp_in0_max : cover property (@(posedge clk) in0 == {WIDTH{1'b1}});
   cp_in1_max : cover property (@(posedge clk) in1 == {WIDTH{1'b1}});

   // These are equivalent to the previous two covers, but uses an alternative
   // way of generating a WIDTH-bit signal of all ones.
   cp_in0_max2 : cover property (@(posedge clk) in0 == WIDTH'(-1));
   cp_in1_max2 : cover property (@(posedge clk) in1 == WIDTH'(-1));

   // For my test in Modelsim, none of the properties except the first two
   // are covered. We'll see how to improve upon this later.
   
endmodule // add_tb 
