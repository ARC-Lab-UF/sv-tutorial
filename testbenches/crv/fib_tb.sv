`timescale 1 ns / 10 ps

class fib_item;

   rand bit go;   
   rand bit [4:0] n;
   rand bit [31:0] result;

   // The sequence starts at 1, so don't test 0.
   constraint c_n_range { n > 0; }

   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass

module fib_tb;

   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;
   int 		     passed, failed, reference;
   
   fib DUT (.*);

   fib_item item;

   function int fib_reference(int n);
      int 	     x, y, i, temp;
      x = 0;
      y = 1;
      i = 3;
      if (n < 2)
	return 0;      
      
      while (i <= n) begin
	 temp = x+y;
	 x = y;
	 y = temp;
	 i ++;	 
      end
      return y;
      
   endfunction
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      item = new;      
      $timeformat(-9, 0, " ns");

      passed = 0;
      failed = 0;      
      
      rst = 1'b1;
      go = 1'b0;
      n = '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;
      
      for (int i=0; i < 10; i++) begin
	 n = $random;
	 go = 1'b1;
	 @(posedge done);
	 reference = fib_reference(n);	 
	 if (result == reference) begin
	    $display("Test passed (time %0t)", $time);
	    passed ++;
	 end
	 else begin
	    $display("Test failed (time %0t): result = %0d instead of %0d.", $time, result, reference);
	    failed ++;	    
	 end

	 go = 1'b0;
	 @(posedge clk);	 
      end

      $display("Tests completed: %0d passed, %0d failed", passed, failed);      
      disable generate_clock;      
   end
     
endmodule
