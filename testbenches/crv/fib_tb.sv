`timescale 1 ns / 10 ps

module fib_tb_basic;

   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;
   int 		     passed, failed, reference;
   
   fib DUT (.*);

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

   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) $rose(go) |=> !done);

   // TODO: check to make sure done stays asserted indefinitely.
      
     
endmodule
/*
class fib_item;

   rand bit go;   
   rand bit [4:0] n;
   rand bit [31:0] result;

   // The sequence starts at 1, so don't test 0.
   constraint c_n_range { n > 0; }

   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass
*/

class fib_item1;
   rand bit [4:0] n;

   // The sequence starts at 1, so don't test 0.
   constraint c_n_range { n > 0; }
endclass


class generator1 #(int num_tests);
   mailbox driver_mailbox;
   event   driver_done_event;
   event   generator_done_event;
   
   task run();
      fib_item1 item = new;
      for (int i=0; i < num_tests; i++) begin
	 if (!item.randomize()) $display("Randomize failed");
	 $display("Time %0t [Generator]: Generating fib input %0d for test %0d.", $time, item.n, i);
	 driver_mailbox.put(item);
	 @(driver_done_event);	 
      end
   
      $display("Time %0t [Generator]: Generator done.", $time);
      -> generator_done_event;      
   endtask
endclass // generator


class driver1;   
   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;

   mailbox driver_mailbox;
   event   driver_done_event;

   task run();
      $display("Time %0t [Driver]: Driver starting.", $time);

      forever begin
	 fib_item1 item; 

	 // Wait for the generator to send an input test to drive.
	 driver_mailbox.get(item);		 
	 $display("Time %0t [Driver]: Driving %0d test.", $time, item.n);

	 n <= item.n;
	 go <= 1'b1;	
	 @(posedge done);
	 go <= 1'b0;
	 @(posedge clk);
	 ->driver_done_event;	 	 	 
      end              
   endtask       
endclass
 

module fib_tb1;

   localparam NUM_TESTS = 100;   
   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;
   int 		     passed, failed, reference;

   mailbox driver_mailbox = new;
   event   driver_done_event;
   event   generator_done_event;   
   generator1 #(.num_tests(NUM_TESTS)) gen = new;
   driver1 drv = new;

   fib DUT (.*);

   always @(drv.go) go = drv.go;
   always @(drv.n) n = drv.n;
   always @(clk) drv.clk = clk;
   always @(done) drv.done = done;
  
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");

      // Initialize the generator and driver.
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
      gen.generator_done_event = generator_done_event;
            
      rst = 1'b1;
      go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;
      @(posedge clk);
      fork
	 gen.run();
	 drv.run();
      join_any
   end

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
   
   always @(posedge done) begin
      reference = fib_reference(n);	 
      if (result == reference) begin
	 $display("Test passed (time %0t)", $time);
	 passed ++;
      end
      else begin
	 $display("Test failed (time %0t): result = %0d instead of %0d.", $time, result, reference);
	 failed ++;	    
      end      
   end // always @ (posedge done)

   initial begin
      @(generator_done_event);
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
      disable generate_clock;      
   end
   
   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) $rose(go) |=> !done);

     
endmodule


interface fib_if (input logic clk);
   logic 	     rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;   
endinterface


class driver2;
   virtual 	     fib_if vif;
   mailbox 	     driver_mailbox;
   event 	     driver_done_event;

   task run();
      $display("Time %0t [Driver]: Driver starting.", $time);

      forever begin
	 fib_item1 item; 

	 // Wait for the generator to send an input test to drive.
	 driver_mailbox.get(item);		 
	 $display("Time %0t [Driver]: Driving %0d test.", $time, item.n);

	 vif.n <= item.n;
	 vif.go <= 1'b1;	
	 @(posedge vif.done);
	 vif.go <= 1'b0;
	 @(posedge vif.clk);
	 -> driver_done_event;	 	 	 
      end              
   endtask       
endclass
 

module fib_tb2;
   
   localparam NUM_TESTS = 100;   
   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;
   int 		     passed, failed, reference;
   
   mailbox 	     driver_mailbox = new;
   event 	     driver_done_event;
   event 	     generator_done_event;   
   generator1 #(.num_tests(NUM_TESTS)) gen = new;
   driver2 drv = new;

   fib_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");

      // Initialize the generator and driver.
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
      gen.generator_done_event = generator_done_event;
      drv.vif = _if;
            
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);
      fork
	 gen.run();
	 drv.run();
      join_any
   end

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
   
   always @(posedge _if.done) begin
      reference = fib_reference(_if.n);	 
      if (_if.result == reference) begin
	 $display("Test passed (time %0t)", $time);
	 passed ++;
      end
      else begin
	 $display("Test failed (time %0t): result = %0d instead of %0d.", $time, _if.result, reference);
	 failed ++;	    
      end      
   end // always @ (posedge done)

   initial begin
      @(generator_done_event);
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
      disable generate_clock;      
   end
   
   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) $rose(go) |=> !done);
     
endmodule // fib_tb2


class fib_item2;
   rand bit [4:0] n;
   bit [31:0] result;
      
   // The sequence starts at 1, so don't test 0.
   constraint c_n_range { n > 0; }
endclass


class monitor1;
   virtual 	     fib_if vif;
   mailbox 	     scoreboard_mailbox;

   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
	 fib_item2 item = new;	
	 @(posedge vif.done);
	 item.n = vif.n;
	 item.result = vif.result;
	 $display("Time %0t [Monitor]: Monitor detected result=%0d for n=%0d.", $time, vif.result, vif.n);
	 scoreboard_mailbox.put(item);
      end
   endtask       
endclass

class scoreboard1;
   mailbox scoreboard_mailbox;
   event   finished_event;   
   int 	   passed, failed, reference;
   
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

   task run();
      passed = 0;
      failed = 0;
            
      forever begin
	 fib_item2 item;
	 scoreboard_mailbox.get(item);

	 reference = fib_reference(item.n);	 
	 if (item.result == reference) begin
	    $display("Time %0t [Scoreboard] Test passed for n=%0d", $time, item.n);
	    passed ++;
	 end
	 else begin
	    $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for n=%0d.", $time, item.result, reference, item.n);
	    failed ++;	    
	 end
      end
   endtask

   function void report_status();     
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass


module fib_tb3;
   
   localparam NUM_TESTS = 100;   
   logic 	     clk, rst, go, done;  
   logic [4:0] 	     n;
   logic [31:0]      result;
   
   mailbox 	     driver_mailbox = new;
   mailbox 	     scoreboard_mailbox = new;
   event 	     driver_done_event;
   event 	     generator_done_event;
   generator1 #(.num_tests(NUM_TESTS)) gen = new;
   driver2 drv = new;
   monitor1 monitor = new;
   scoreboard1 scoreboard = new;
   
   fib_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");

      // Initialize the generator and driver.
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
      gen.generator_done_event = generator_done_event;
      drv.vif = _if;
      monitor.vif = _if;
      monitor.scoreboard_mailbox = scoreboard_mailbox;
      scoreboard.scoreboard_mailbox = scoreboard_mailbox;      
            
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);
      fork
	 gen.run();
	 drv.run();
	 monitor.run();
	 scoreboard.run();	 
      join_any
   end
      
   initial begin
      @(generator_done_event);
      scoreboard.report_status();
      disable generate_clock;      
   end
   
   assert property (@(posedge clk) $rose(go) |=> !done);
     
endmodule // fib_tb3



class env #(int num_tests);

   generator1 #(.num_tests(num_tests)) gen;
   driver2 drv;
   monitor1 monitor;
   scoreboard1 scoreboard;
   virtual fib_if vif;
   
   mailbox scoreboard_mailbox;
   mailbox driver_mailbox;
   
   event 	     driver_done_event;
   event 	     generator_done_event;
   
   function new();
      gen = new;
      drv = new;
      monitor = new;
      scoreboard = new;
      scoreboard_mailbox = new;
      driver_mailbox = new;
   endfunction // new

   virtual 	     task run();
      drv.vif = vif;
      monitor.vif = vif;
          
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;

      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
                     
      monitor.scoreboard_mailbox = scoreboard_mailbox;
      scoreboard.scoreboard_mailbox = scoreboard_mailbox;
      
      fork
	 gen.run();
	 drv.run();
	 monitor.run();
	 scoreboard.run();	 
      join_any

      scoreboard.report_status();      
   endtask // run   
endclass


module fib_tb4;
   
   localparam NUM_TESTS = 100;
   logic 	     clk;
   env #(.num_tests(NUM_TESTS)) _env = new;
   
   fib_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin      
      $timeformat(-9, 0, " ns");
      _env.vif = _if;      
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);     
      _env.run();
      disable generate_clock;      
   end
         
   assert property (@(posedge _if.clk) $rose(_if.go) |=> !_if.done);
     
endmodule // fib_tb4


class fib_item3;   
   rand bit [4:0] n;
   rand bit go;
   bit [31:0] result;
   
   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }       
endclass

class generator2;
   mailbox driver_mailbox;
   event   driver_done_event;
  
   task run();
      fib_item3 item = new;

      forever begin	 
	 if (!item.randomize()) $display("Randomize failed");
	 //$display("Time %0t [Generator]: Generating fib input %0d, go=%0b.", $time, item.n, item.go);
	 driver_mailbox.put(item);
	 @(driver_done_event);
      end
   endtask
endclass // generator2


class driver3;
   virtual 	     fib_if vif;
   mailbox 	     driver_mailbox;
   mailbox 	     scoreboard_n_mailbox;
   event 	     driver_done_event;

   task run();
      logic is_first_test = 1'b1;      
      logic is_active = 1'b0;
      $display("Time %0t [Driver]: Driver starting.", $time);
            
      forever begin
	 fib_item3 item;

	 //@(posedge vif.clk);
	 
	 // If the circuit is reset at any point, reset the driver state.
	 while (vif.rst) begin
	    @(posedge vif.clk);	  
	    is_first_test = 1'b1;
	    is_active = 1'b0;	    	    
	 end
	 
	 // Wait for the generator to send an input to drive. Unlike before,
	 // the generator now delivers inputs every cycle, and includes the
	 // go signal in order to test assertions of go while the DUT is already
	 // active.
	 driver_mailbox.get(item);
	 //$display("Time %0t [Driver]: Driving n=%0d, go=%0b.", $time, item.n, item.go);
	 
	 // For this driver, we drive both the n and go inputs directly from the
	 // generator.
	 vif.n = item.n;
	 vif.go = item.go;

	 // Wait until the next clock edge where the inputs will be seen.
	 // This is needed here because signals haven't changed yet on the
	 // current clock cycle. So, if done is about to change, we won't see
	 // it. That would cause the following code to mistake the DUT as
	 // being active, which could prevent sending the test to the
	 // scoreboard.
	 @(posedge vif.clk);
	 	 
	 // If done is asserted and go isn't, or if this is the first_test, 
	 // then the DUT should be inactive and ready for another test.  
	 if (vif.done || is_first_test)
	   is_active = 1'b0;
	 	 
	 //if (vif.n == 2)
	 //  $display("Time %0t [Driver]: DEBUG n=%0d, is_active=%0b, go=%0b, done=%0b.", $time, vif.n, is_active, vif.go, vif.done);
	 	 
	 // If the DUT isn't already active, and we get a go signal, we are
	 // starting a test, so inform the scoreboard. The scoreboard will
	 // then wait to get the result from the monitor. This strategy allows
	 // the testbench to test assertions of go that don't correspond to
	 // the start of a test because the DUT is already active. The DUT
	 // should ignore these assertions.
	 if (!is_active && vif.go) begin	    
	    $display("Time %0t [Driver]: Sending start of test for n=%0d.", $time, item.n);
	    scoreboard_n_mailbox.put(item);
	    is_active = 1'b1;	    
	    is_first_test = 1'b0;
	 end

	 -> driver_done_event;	 
      end              
   endtask       
endclass

class monitor2;
   virtual 	     fib_if vif;
   mailbox 	     scoreboard_result_mailbox;

   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
	 fib_item3 item = new;	
	 @(posedge vif.done);
	 // In this version, we only care about the result, because the driver
	 // already informed the scoreboard of the next n value to check.
	 item.result = vif.result;
	 $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, vif.result);
	 scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


class scoreboard2 #(int num_tests);
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_n_mailbox;
   int 	   passed, failed, reference;
   
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

   task run();
      passed = 0;
      failed = 0;

      for (int i=0; i < num_tests; i++) begin
	 fib_item3 in_item, out_item;
	 fib_item3 final_item = new;

	 // First wait until the driver informs us of a new test.
	 scoreboard_n_mailbox.get(in_item);
	 $display("Time %0t [Scoreboard]: Received start of test for n=%0d.", $time, in_item.n);

	 // Save the n value, otherwise it will be lost.
	 final_item.n = in_item.n;
	 	 
	 // Then, wait until the monitor tells us that test is complete.
	 scoreboard_result_mailbox.get(out_item);
	 $display("Time %0t [Scoreboard]: Received result=%0d for n=%0d.", $time, out_item.result, final_item.n);
 
	 final_item.result = out_item.result;

	 // Get the correct result based on the n value at the start of the
	 // test.
	 reference = fib_reference(final_item.n);	 
	 if (final_item.result == reference) begin
	    $display("Time %0t [Scoreboard] Test passed for n=%0d", $time, final_item.n);
	    passed ++;
	 end
	 else begin
	    $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for n=%0d.", $time, final_item.result, reference, final_item.n);
	    failed ++;	    
	 end
      end
   endtask

   function void report_status();     
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass // scoreboard2

class env2 #(int num_tests);

   generator2 gen;
   driver3 drv;
   monitor2 monitor;
   scoreboard2 #(.num_tests(num_tests)) scoreboard;
   virtual fib_if vif;
   
   mailbox scoreboard_n_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
      
   function new();
      gen = new;
      drv = new;
      monitor = new;
      scoreboard = new;
      scoreboard_n_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
   endfunction // new

   virtual 	     task run();
      drv.vif = vif;
      monitor.vif = vif;
      
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      
      drv.scoreboard_n_mailbox = scoreboard_n_mailbox;
      scoreboard.scoreboard_n_mailbox = scoreboard_n_mailbox;
      
      monitor.scoreboard_result_mailbox = scoreboard_result_mailbox;
      scoreboard.scoreboard_result_mailbox = scoreboard_result_mailbox;
   
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
         
      fork
	 gen.run();
	 drv.run();
	 monitor.run();
	 scoreboard.run();	 
      join_any

      scoreboard.report_status();      
   endtask // run   
endclass


module fib_tb5;
   
   localparam NUM_TESTS = 1000;
   logic 	     clk;
   env2 #(.num_tests(NUM_TESTS)) _env = new;
   
   fib_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin      
      $timeformat(-9, 0, " ns");
      _env.vif = _if;      
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);     
      _env.run();
      disable generate_clock;      
   end
      
   assert property (@(posedge _if.clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
     
endmodule // fib_tb5


// TODO illustate tests with multiple test sizes, repeats, different generation
// strategies (increment vs random).

class generator3;
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      fib_item3 item = new;

      forever begin	 
	 if (!item.randomize()) $display("Randomize failed");
	 //$display("Time %0t [Generator]: Generating fib input %0d, go=%0b.", $time, item.n, item.go);
	 driver_mailbox.put(item);
	 @(driver_done_event);
      end
   endtask
endclass // generator3


class driver4;   
   virtual 	     fib_if vif;
   mailbox 	     driver_mailbox;
   mailbox 	     scoreboard_n_mailbox;
   event 	     driver_done_event;

   function new(virtual fib_if _vif, mailbox _driver_mailbox, 
		mailbox _scoreboard_n_mailbox, event _driver_done_event);
      vif = _vif;      
      driver_mailbox = _driver_mailbox;
      scoreboard_n_mailbox = _scoreboard_n_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      logic is_first_test = 1'b1;      
      logic is_active = 1'b0;
      $display("Time %0t [Driver]: Driver starting.", $time);
            
      forever begin
	 fib_item3 item;

	 //@(posedge vif.clk);
	 
	 // If the circuit is reset at any point, reset the driver state.
	 while (vif.rst) begin
	    @(posedge vif.clk);	  
	    is_first_test = 1'b1;
	    is_active = 1'b0;	    	    
	 end
	 
	 // Wait for the generator to send an input to drive. Unlike before,
	 // the generator now delivers inputs every cycle, and includes the
	 // go signal in order to test assertions of go while the DUT is already
	 // active.
	 driver_mailbox.get(item);
	 //$display("Time %0t [Driver]: Driving n=%0d, go=%0b.", $time, item.n, item.go);
	 
	 // For this driver, we drive both the n and go inputs directly from the
	 // generator.
	 vif.n = item.n;
	 vif.go = item.go;

	 // Wait until the next clock edge where the inputs will be seen.
	 // This is needed here because signals haven't changed yet on the
	 // current clock cycle. So, if done is about to change, we won't see
	 // it. That would cause the following code to mistake the DUT as
	 // being active, which could prevent sending the test to the
	 // scoreboard.
	 @(posedge vif.clk);
	 	 
	 // If done is asserted and go isn't, or if this is the first_test, 
	 // then the DUT should be inactive and ready for another test.  
	 if (vif.done || is_first_test)
	   is_active = 1'b0;
	 	 
	 //if (vif.n == 2)
	 //  $display("Time %0t [Driver]: DEBUG n=%0d, is_active=%0b, go=%0b, done=%0b.", $time, vif.n, is_active, vif.go, vif.done);
	 	 
	 // If the DUT isn't already active, and we get a go signal, we are
	 // starting a test, so inform the scoreboard. The scoreboard will
	 // then wait to get the result from the monitor. This strategy allows
	 // the testbench to test assertions of go that don't correspond to
	 // the start of a test because the DUT is already active. The DUT
	 // should ignore these assertions.
	 if (!is_active && vif.go) begin	    
	    $display("Time %0t [Driver]: Sending start of test for n=%0d.", $time, item.n);
	    scoreboard_n_mailbox.put(item);
	    is_active = 1'b1;	    
	    is_first_test = 1'b0;
	 end

	 -> driver_done_event;	 
      end              
   endtask       
endclass


class monitor3;
   virtual 	     fib_if vif;
   mailbox 	     scoreboard_result_mailbox;

   function new(virtual fib_if _vif, mailbox _scoreboard_result_mailbox);
      vif = _vif;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
      
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
	 fib_item3 item = new;	
	 @(posedge vif.done);
	 // In this version, we only care about the result, because the driver
	 // already informed the scoreboard of the next n value to check.
	 item.result = vif.result;
	 $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, vif.result);
	 scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


class scoreboard3 #(int num_tests);
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_n_mailbox;
   int 	   passed, failed, reference;

   function new(mailbox _scoreboard_n_mailbox, mailbox _scoreboard_result_mailbox);
      scoreboard_n_mailbox = _scoreboard_n_mailbox;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;
   endfunction // new
   
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

   task run();
      passed = 0;
      failed = 0;

      for (int i=0; i < num_tests; i++) begin
	 fib_item3 in_item, out_item;
	 fib_item3 final_item = new;

	 // First wait until the driver informs us of a new test.
	 scoreboard_n_mailbox.get(in_item);
	 $display("Time %0t [Scoreboard]: Received start of test for n=%0d.", $time, in_item.n);

	 // Save the n value, otherwise it will be lost.
	 final_item.n = in_item.n;
	 	 
	 // Then, wait until the monitor tells us that test is complete.
	 scoreboard_result_mailbox.get(out_item);
	 $display("Time %0t [Scoreboard]: Received result=%0d for n=%0d.", $time, out_item.result, final_item.n);
 
	 final_item.result = out_item.result;

	 // Get the correct result based on the n value at the start of the
	 // test.
	 reference = fib_reference(final_item.n);	 
	 if (final_item.result == reference) begin
	    $display("Time %0t [Scoreboard] Test passed for n=%0d", $time, final_item.n);
	    passed ++;
	 end
	 else begin
	    $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for n=%0d.", $time, final_item.result, reference, final_item.n);
	    failed ++;	    
	 end
      end
   endtask

   function void report_status();     
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass // scoreboard3


class env3 #(int num_tests);

   generator3 gen;
   driver4 drv;
   monitor3 monitor;
   scoreboard3 #(.num_tests(num_tests)) scoreboard;
   
   mailbox scoreboard_n_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
      
   function new(virtual fib_if vif);      
      scoreboard_n_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;

      // This is a much less error-prone way to create the environment. In the
      // previous version, we instaniated each of these classes and then
      // connected their internal signals within the environment. The risk
      // with that approach is that we don't get any compiler errors. The errors
      // will only show up during simulation.
      // With this new approach, we only construct each instance when we have
      // all the information we need for it. In other words, every object is
      // fully initialized upon construction. If we leave out required
      // parameters from the constructor, we will get compiler errors, which is
      // what we want. Our goal is to always catch as many problems as possible
      // at compile time.
      
      gen = new(driver_mailbox, driver_done_event);
      drv = new(vif, driver_mailbox, scoreboard_n_mailbox, driver_done_event);
      monitor = new(vif, scoreboard_result_mailbox);
      scoreboard = new(scoreboard_n_mailbox, scoreboard_result_mailbox);
   endfunction // new

   virtual 	     task run();      
      fork
	 gen.run();
	 drv.run();
	 monitor.run();
	 scoreboard.run();	 
      join_any

      scoreboard.report_status();      
   endtask // run   
endclass


module fib_tb6;
   
   localparam NUM_TESTS = 10000;
   logic 	     clk;
   
   fib_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));

   // Pass the interface to the constructor so that the environment isn't
   // created in an invalid state that requires further initialization.
   env3 #(.num_tests(NUM_TESTS)) _env = new(_if);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin      
      $timeformat(-9, 0, " ns");
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);     
      _env.run();
      disable generate_clock;      
   end
      
   assert property (@(posedge _if.clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
     
endmodule // fib_tb6
