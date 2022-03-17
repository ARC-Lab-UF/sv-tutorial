// Greg Stitt
// University of Florida

`include "test.svh"

module bit_diff_tb;
      
   localparam NUM_RANDOM_TESTS = 1000;
   localparam NUM_CONSECUTIVE_TESTS = 200;
   localparam NUM_REPEATS = 4;   
   localparam WIDTH = 16;   
   logic             clk;
   
   bit_diff_bfm #(.WIDTH(WIDTH)) bfm (.clk(clk));   
   bit_diff #(.WIDTH(WIDTH)) DUT (.clk(clk), .rst(bfm.rst), .go(bfm.go), 
                                  .done(bfm.done), .data(bfm.data), 
                                  .result(bfm.result));

   random_test #(.WIDTH(WIDTH)) test_random = new(bfm, "Random Test");
   consecutive_test #(.WIDTH(WIDTH)) test_consecutive = new(bfm, "Consecutive Test"); 
     
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");
      test_random.run(NUM_RANDOM_TESTS, NUM_REPEATS);      
      test_consecutive.run(NUM_CONSECUTIVE_TESTS, NUM_REPEATS);
      test_random.report_status();
      test_consecutive.report_status();      
      disable generate_clock;      
   end
      
   assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.go && bfm.done |=> !bfm.done);
   assert property (@(posedge bfm.clk) disable iff (bfm.rst) $fell(bfm.done) |-> $past(bfm.go,1));
     
endmodule
