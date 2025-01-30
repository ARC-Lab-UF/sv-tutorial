// Greg Stitt
// University of Florida
//
// This file includes a collection of testbenches for the included add module
// that illustrate different coverage strategies.

`timescale 1 ns / 10 ps

// Module: add_tb1
// Description: A testbench that uses cover properties to track whether or not
// specific properties are ever true.
module add_tb1 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 16
);
    logic [WIDTH-1:0] in0, in1;
    logic [WIDTH-1:0] sum;
    logic carry_out, carry_in;

    add #(.WIDTH(WIDTH)) DUT (.*);

    // The adder doesn't have a clock, but we can still use one in the testbench
    // to coordinate assertion and cover properties.
    logic clk = 1'b0;
    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Generate random tests for all inputs.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in0 <= $urandom;
            in1 <= $urandom;
            carry_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // These assertions will report errors if there are any incorrect outputs.
    logic [WIDTH:0] full_sum;
    assign full_sum = {1'b0, in0} + in1 + carry_in;
    assert property (@(posedge clk) sum == full_sum[WIDTH-1:0]);
    assert property (@(posedge clk) carry_out == full_sum[WIDTH]);

    // I prefer the following, but the second one breaks my formatter.
    //assert property (@(posedge clk) sum == in0 + in1 + carry_in);
    //assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);

    // However, those assertions don't guarantee that we've tested everything.
    // We could use cover properties to make sure that the testbench actually
    // tests the situations that are most likely to cause errors.
    //
    // For example, these make sure there was at least one test where there 
    // was a carry in, and at least one test that generated a carry out.
    cp_carry_in :
    cover property (@(posedge clk) carry_in);
    cp_carry_out :
    cover property (@(posedge clk) carry_out);

    // Here we check to make sure that both inputs were 0 at some point.
    cp_in0_eq_0 :
    cover property (@(posedge clk) in0 == 0);
    cp_in1_eq_0 :
    cover property (@(posedge clk) in1 == 0);

    // Here we check to make sure both inputs are tested with their maximum
    // amounts. To get the maximum amount, we use the replication operator.
    cp_in0_max :
    cover property (@(posedge clk) in0 == {WIDTH{1'b1}});
    cp_in1_max :
    cover property (@(posedge clk) in1 == {WIDTH{1'b1}});

    // These are equivalent to the previous two covers, but use an alternative
    // way of generating a WIDTH-bit signal of all ones. In general, any integer
    // expression can be extended or truncated to a specific number of bits
    // by specifying the width (as a constant or literal) followed by the
    // expression in parantheses.
    // VHDL Comparison: this construct is similar to the to_unsigned or to_signed
    // fuctions in numeric_std.
    //cp_in0_max2 : cover property (@(posedge clk) in0 == WIDTH'(-1));
    //cp_in1_max2 : cover property (@(posedge clk) in1 == WIDTH'(-1));

    // Or, we could simply do it like this:
    //cp_in0_max3 :
    //cover property (@(posedge clk) in0 == '1);
    //cp_in1_max3 :
    //cover property (@(posedge clk) in1 == '1);

    // For my test in Questa, none of the properties except the first two
    // are covered. We'll see how to improve upon this later.

endmodule  // add_tb1 


// Module: add_tb2
// Description: This testbench improves upon the previous one by adding tests
// to ensure all the properties are covered.

module add_tb2 #(
    parameter RANDOM_TESTS = 1000,
    parameter ZERO_TESTS = 100,
    parameter MAX_TESTS = 100,
    parameter int WIDTH = 16
);
    logic [WIDTH-1:0] in0, in1;
    logic [WIDTH-1:0] sum;
    logic carry_out, carry_in;

    add #(.WIDTH(WIDTH)) DUT (.*);

    // The adder doesn't have a clock, but we can still use one in the testbench
    // to coordinate assertion and cover properties.
    logic clk = 1'b0;
    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end
    
    initial begin
        $timeformat(-9, 0, " ns");

        // Random tests.
        for (int i = 0; i < RANDOM_TESTS; i++) begin
            in0 <= $urandom;
            in1 <= $urandom;
            carry_in <= $urandom;
            @(posedge clk);
        end

        // The previous testbench makes it unlikely for values of 0 to be used
        // in the simulation. Here, we explicitly test each input with 0s.
        // in0 == 0 tests.
        for (int i = 0; i < ZERO_TESTS; i++) begin
            in0 <= '0;
            in1 <= $urandom;
            carry_in <= $urandom;
            @(posedge clk);
        end

        // in1 == 0 tests.
        for (int i = 0; i < ZERO_TESTS; i++) begin
            in0 <= $urandom;
            in1 <= '0;
            carry_in <= $urandom;
            @(posedge clk);
        end

        // Similarly, we add tests with the maximum value of both inputs.
        // Ideally, you would probably also want to test both inputs with their
        // maximum values at the same time, which we omit here.
        // in0 == MAX tests.
        for (int i = 0; i < MAX_TESTS; i++) begin
            in0 <= '1;
            in1 <= $urandom;
            carry_in <= $urandom;
            @(posedge clk);
        end

        // in1 == MAX tests.
        for (int i = 0; i < MAX_TESTS; i++) begin
            in0 <= $urandom;
            in1 <= '1;
            carry_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // This testbench performs the same assertions and covers as before, but
    // now we should see everything pass.
    logic [WIDTH:0] full_sum;
    assign full_sum = {1'b0, in0} + in1 + carry_in;
    assert property (@(posedge clk) sum == full_sum[WIDTH-1:0]);
    assert property (@(posedge clk) carry_out == full_sum[WIDTH]);

    cp_carry_in :
    cover property (@(posedge clk) carry_in);
    cp_carry_out :
    cover property (@(posedge clk) carry_out);

    cp_in0_eq_0 :
    cover property (@(posedge clk) in0 == 0);
    cp_in1_eq_0 :
    cover property (@(posedge clk) in1 == 0);

    cp_in0_max :
    cover property (@(posedge clk) in0 == {WIDTH{1'b1}});
    cp_in1_max :
    cover property (@(posedge clk) in1 == {WIDTH{1'b1}});

endmodule

/*
// Module: add_tb3
// Description: This testbench shows alternative cover constructs:
// covergroups and coverpoints. Whereas cover properties work well for specific
// properties, those properties don't easily give much information about the
// range of values tested. Covergroups and points provide a convenient construct
// for such coverage.

module add_tb3;

   localparam WIDTH = 16;
   localparam RANDOM_TESTS = 1000;
   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic             carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic             clk;

   // Here we use a covergroup that will test coverage of different possible
   // values for whatever we request, where values are sampled on every rising
   // clock edge.
   covergroup cg @(posedge clk);
      // Coverpoints specify variables (or other cover points) that should be
      // sampled. By default, each coverpoint will have all its possible values
      // divided up into at most 64 bins. For these two variables, there are
      // only two possible values, so there will be a bin for 1'b0 occurrences 
      // and a bin for 1'b1 occurences.
      cin : coverpoint carry_in;
      cout : coverpoint carry_out;
      
      // This will similarly track values of in0 and in1, but since these will
      // have far more values for any reasonable WIDTH parameter, most
      // situations will divide up all the values into 64 bins, and track
      // occurences of values that fall into each bin.
      in0_bin : coverpoint in0;
      in1_bin : coverpoint in1;

      // If you want more (or fewer) bins, you can use the option.auto_bin_max
      // parameter. For example, the following will do coverage of all 
      // possible in0 values by creating a separate bin for each possible 
      // value. NOTE: using this strategy for any significant WIDTH will run 
      // out of memory. 
      in0_complete : coverpoint in0 {option.auto_bin_max = 2**WIDTH;}

      // These are two ways of checking all possible combinations of in0 and
      // in1, either by coverpoint name, or variable name. This technique is
      // called cross coverage.
      //
      // For this cross, we are crossing existing coverpoints. Because each of
      // those points most likely has 64 bins, the cross coverage will have
      // 64*64 = 4096 bins. Because this testbench is only performing 1000
      // random tests, it is impossible for us to achieve 100% coverage here.
      in0_cross_in1 : cross in0_bin, in1_bin;

      // Here we perform a cross of all the input values. I can't find the
      // exact language definition, but it appears that these inputs are binned
      // first before being crossed, which makes this cross equivalent to the
      // previous one.
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
         in0 <= $urandom;
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 <= 0;
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 <= $urandom;
         in1 <= 0;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 <= {WIDTH{1'b1}};
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 <= $urandom;
         in1 <= {WIDTH{1'b1}};
         carry_in <= $urandom;             
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


// Module: add_tb4
// Description: Normally, coverage is defined independently of the testbench. 
// For example, we might define coverage as consisting of the following tests:
// -Make sure we test at least 100 examples with a carry in.
// -Make sure we test at least 10 examples where a carry out is produced.
// -Make sure each input is tested with a value of 0 at least 10 times.
// -Make sure each input is tested with a max value at least 10 times.
// -If we divide up the range of all input values into 16 bins, make sure at
//  all bins occur at least once during the testing.
// -Make sure all combinations of the 16 bins are tested for both inputs.
// -Make sure that we test both inputs with 0 at the same time.
// -Make sure we test both inputs with a max value at the same time.
//
// This testbench shows how to create covergroups and points to check for this
// coverage, while also extending the tests to ensure we achieve 100% coverage.

module add_tb4;

   localparam WIDTH = 16;

   // To achieve 100% coverage for a WIDTH of 16, this parameter had to be
   // increased to ensure that cross coverage has achieved for the input
   // combinations.
   localparam RANDOM_TESTS = 10000;
   //localparam RANDOM_TESTS = 1000;

   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic             carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic             clk;
   covergroup cg @(posedge clk);
      // Make sure the carry_in is asserted at least 100 times.
      cin : coverpoint carry_in {bins one = {1}; option.at_least = 100;}
      // Make sure the carry out is generated at least 10 times.
      cout : coverpoint carry_out {bins one = {1}; option.at_least = 10;}

      // Make sure that in0 has a 0 and max value tested at least 10 times.
      in0_extremes : coverpoint in0 {
         bins zero = {0};
         bins max_ = {{WIDTH{1'b1}}};
         option.at_least = 10; 
      }
      // Make sure that in1 has a 0 and max value tested at least 10 times.
      in1_extremes : coverpoint in1 {
         bins zero = {0};
         bins max_ = {{WIDTH{1'b1}}};
         option.at_least = 10; 
      }

      // Divide up the input space into 16 bins and make sure all bins are
      // tested at least once.
      in0_full : coverpoint in0 {option.auto_bin_max = 16;}
      in1_full : coverpoint in1 {option.auto_bin_max = 16;}
       
      // Make sure all combinations of input bins are tested at least once.
      in0_cross_in1 : cross in0_full, in1_full;

      // Check to make sure both inputs are 0 or the max value at the same time.
      // It would be more readable to use cover properties here, but if we
      // want this included in the coverage reporting for the group, we need it
      // here.
      in0_in1_eq_0 : coverpoint (in0==0 && in1==0) {bins true = {1'b1};}
      in0_in1_eq_max : coverpoint (in0=={WIDTH{1'b1}} && in1=={WIDTH{1'b1}}) {bins true = {1'b1};}
           
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
         in0 <= $urandom;
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 <= 0;
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 <= $urandom;
         in1 <= 0;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 <= {WIDTH{1'b1}};
         in1 <= $urandom;
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 <= $urandom;
         in1 <= {WIDTH{1'b1}};
         carry_in <= $urandom;             
         @(posedge clk);
      end

      // Test both inputs at 0 to achieve 100% coverage.
      for (int i=0; i < 2; i++) begin
         in0 <= 0;
         in1 <= 0;
         carry_in <= i;           
         @(posedge clk);
      end

      // Test both inputs with their maximum values to achieve 100% coverage.
      for (int i=0; i < 2; i++) begin
         // Another way of setting all the bits to 1.
         in0 <= '1;
         in1 <= '1;       
         carry_in <= i;   
         @(posedge clk);
      end
            
      $display("Tests completed.");
      $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());      
      disable generate_clock;      
   end

   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);
   
endmodule
*/
