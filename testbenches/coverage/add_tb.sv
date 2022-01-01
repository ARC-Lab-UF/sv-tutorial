// Greg Stitt
// University of Florida

`timescale 1 ns / 10 ps

module add_tb1;

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
      $timeformat(-9, 0, " ns");

      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
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
   //cp_in0_max2 : cover property (@(posedge clk) in0 == WIDTH'(-1));
   //cp_in1_max2 : cover property (@(posedge clk) in1 == WIDTH'(-1));

   // For my test in Modelsim, none of the properties except the first two
   // are covered. We'll see how to improve upon this later.
   
endmodule // add_tb1 


module add_tb2;

   localparam WIDTH = 16;
   localparam RANDOM_TESTS = 1000;
   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);
   
   logic 	     clk;
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin
      $timeformat(-9, 0, " ns");

      // Random tests.
      for (int i=0; i < RANDOM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = 0;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = $random;
	 in1 = 0;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = {WIDTH{1'b1}};
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = $random;
	 in1 = {WIDTH{1'b1}};
	 carry_in = $random;	 	 
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

endmodule


module add_tb3;

   localparam WIDTH = 16;
   localparam RANDOM_TESTS = 1000;
   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic 	     clk;
   covergroup cg @(posedge clk);
      cin : coverpoint carry_in;
      cout : coverpoint carry_out;

      // Automatically divides up all possible values into bins and counts
      // occurrences of a value falling within each bin. The default bin count
      // is 64, which can be changed with option.auto_bin_max as shown below.
      in0_bin : coverpoint in0;
      in1_bin : coverpoint in1;

      // This will do coverage of all possible in0 values by creating a
      // separate bin for each possible value. NOTE: using this strategy
      // for any significant WIDTH will run out of memory. 
      in0_complete : coverpoint in0 {option.auto_bin_max = 2**WIDTH;}

      // These are two ways of checking all possible combinations of in0 and
      // in1, either by coverpoint name, or variable name. This technique is
      // called cross coverage.
      in0_cross_in1 : cross in0_bin, in1_bin;
      //in0_cross_in1_2 : cross in0, in1;      
            
   endgroup
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   cg cg_inst;      
   initial begin
      cg_inst = new();      
      $timeformat(-9, 0, " ns");
      
      // Random tests.
      for (int i=0; i < RANDOM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = 0;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = $random;
	 in1 = 0;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = {WIDTH{1'b1}};
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = $random;
	 in1 = {WIDTH{1'b1}};
	 carry_in = $random;	 	 
	 @(posedge clk);
      end
            
      $display("Tests completed.");
      $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());      
      disable generate_clock;      
   end

   // These assertions will report errors if there are any incorrect outputs.
   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);

   
endmodule // add_tb3


module add_tb4;

   localparam WIDTH = 16;
   localparam RANDOM_TESTS = 1000;
   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic 	     clk;
   covergroup cg @(posedge clk);
      cin : coverpoint carry_in;
      cout : coverpoint carry_out;

      cp_in0 : coverpoint in0 {
	 bins zero = {0};
	 bins max_ = {{WIDTH{1'b1}}};
	 option.at_least = 2; 
      }
      cp_in1 : coverpoint in0 {
	 bins zero = {0};
	 bins max_ = {{WIDTH{1'b1}}};
	 option.at_least = 2; 
      }

      //in0_cross_in1 : cross in0, in1 {option.cross_auto_bin_max = 32;}
      //in0_cross_in1 : cross in0, in1 {option.auto_bin_max = 16;}
            
   endgroup
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   cg cg_inst;      
   initial begin
      cg_inst = new();      
      $timeformat(-9, 0, " ns");
      
      // Random tests.
      for (int i=0; i < RANDOM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = 0;
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
	 in0 = $random;
	 in1 = 0;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = {WIDTH{1'b1}};
	 in1 = $random;
	 carry_in = $random;	 	 
	 @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
	 in0 = $random;
	 in1 = {WIDTH{1'b1}};
	 carry_in = $random;	 	 
	 @(posedge clk);
      end
            
      $display("Tests completed.");
      $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());      
      disable generate_clock;      
   end

   // These assertions will report errors if there are any incorrect outputs.
   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);

   
endmodule
