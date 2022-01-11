`timescale 1 ns / 10 ps

module bit_diff_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 10000;
   
   logic 	     clk, rst, go, done;  
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;
   int 					passed, failed, reference;
   
   bit_diff_fsmd_1p #(WIDTH) DUT (.*);

   // Reference model for correct result.
   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");

      passed = 0;
      failed = 0;      
      
      rst = 1'b1;
      go = 1'b0;
      data = '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 data = $random;
	 go = 1'b1;
	 @(posedge clk);
	 go = 1'b0;
	 
	 // Works for registered outputs, but not safe for glitches
	 // Test bit
	 //@(posedge done);

	 // Ideal: wait until done is cleared on an edge, and then asserted on
	 // an edge.
	 @(posedge clk iff (done == 1'b0));
	 //$display("Done is 0 (time %0t).", $time);	 
	 @(posedge clk iff (done == 1'b1));
	 //$display("Done is 1 (time %0t).", $time);

	 // Works, but not concise
	 /*while(1) begin
	    @(posedge clk);
	    if (done) break;	    
	 end */ 
	 	 
	 reference = model(data, WIDTH);	 
	 if (result == reference) begin
	    passed ++;
	 end
	 else begin
	    $display("Test failed (time %0t): result = %0d instead of %0d.", $time, result, reference);
	    failed ++;	    
	 end	
      end

      $display("Tests completed: %0d passed, %0d failed", passed, failed);      
      disable generate_clock;      
   end

   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) disable iff (rst) go && done |=> !done);
   
endmodule



module bit_diff_tb2;

   localparam WIDTH = 4;
   localparam NUM_TESTS = 1000;
   
   logic 	     clk, rst, go, done;  
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;
   int 					passed, failed, reference;
   
   bit_diff_fsmd #(WIDTH) DUT (.*);

   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");

      passed = 0;
      failed = 0;      
      
      rst = 1'b1;
      go = 1'b0;
      data = '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;
      
      for (int i=0; i < NUM_TESTS; i++) begin
	 data = $random;
	 go = 1'b1;
	 @(posedge clk);
	 go = 1'b0;	 
	 @(posedge done);
	 reference = model(data, WIDTH);	 
	 if (result == reference) begin
	    $display("Test passed (time %0t)", $time);
	    passed ++;
	 end
	 else begin
	    $display("Test failed (time %0t): result = %0d instead of %0d.", $time, result, reference);
	    failed ++;	    
	 end	
      end

      $display("Tests completed: %0d passed, %0d failed", passed, failed);      
      disable generate_clock;      
   end

   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) disable iff (rst) go && done |=> !done);
   
endmodule
