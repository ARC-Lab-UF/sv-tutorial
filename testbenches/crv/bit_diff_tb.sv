// Greg Stitt
// University of Florida
//
// This file contains a collection of testbenches that graduate evolve a simple
// testbench into a more complex constrained-random verfication (CRV) testbench
// that would be used to test more complex modules.

`timescale 1 ns / 10 ps

// Module: bit_diff_tb_basic
// Description: Follows the simple template seen so far. Although simple, this
// template has significant limitations that become more apparent when doing
// more complex tests that are required for more complex modules.
//
// Specificially, a testbench often has 4 primary parts:
// -Generation of test sequences that stimulate the DUT
// -A driver that converts that test sequences into DUT pin values
// -A monitor that checks the DUT outputs when new results or other behaviors
// -A scoreboard that compares any results from the monitor with correct values
//  based on the a reference model that is applied to the same test sequences.
//
// The primary limitation of this simple testbench is that it does all these
// parts in the same region of code. This makes it hard to modify one part
// without affecting the others. It also makes it hard for other people to
// understand the purpose of the code. Finally, it doesn't scale well to
// complicated tests, and multiple types of tests.
//
// So, we'll first understand this basic testbench and then gradually transform
// it into something where the different parts are isolated from each other.

module bit_diff_tb_basic;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 16;
   
   logic 	     clk, rst, go, done;  
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   // Testbench variables
   int 					passed, failed, reference;

   // Instantiate the DUT
   bit_diff #(.WIDTH(WIDTH)) DUT (.*);

   // Reference model for getting the correct result.
   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction
   
   // Generate the clock.
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   // Do everything else.
   initial begin
      $timeformat(-9, 0, " ns");

      passed = 0;
      failed = 0;      

      // Reset the design.
      rst = 1'b1;
      go = 1'b0;
      data = '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;

      // Perform NUM_TESTS number of randome tests.
      for (int i=0; i < NUM_TESTS; i++) begin
	 data = $random;
	 go = 1'b1;
	 @(posedge clk);
	 go = 1'b0;
	 
	 // Works for registered outputs, but not safe for glitches that may
	 // occur from combinational logic outputs.
	 // Test bit_diff_fsmd_2p for an example of where this fails.
	 //@(posedge done);

	 // Instead, wait until done is cleared on an edge, and then asserted 
	 // on an edge.
	 @(posedge clk iff (done == 1'b0));
	 //$display("Done is 0 (time %0t).", $time);	 
	 @(posedge clk iff (done == 1'b1));
	 //$display("Done is 1 (time %0t).", $time);

	 // Similar strategy, but less concise
	 /*while(1) begin
	    @(posedge clk);
	    if (done) break;	    
	 end */ 

	 // Compare the output with the reference model.
	 reference = model(data, WIDTH);	 
	 if (result == reference) begin
	    $display("Test passed (time %0t) for input = %h", $time, data);
	    passed ++;
	 end
	 else begin
	    $display("Test failed (time %0t): result = %0d instead of %0d for input = %h.", $time, result, reference, data);
	    failed ++;	    
	 end	
      end

      $display("Tests completed: %0d passed, %0d failed", passed, failed);      
      disable generate_clock;      
   end   

   // Check to make sure done cleared within a cycle.
   assert property (@(posedge clk) disable iff (rst) go && done |=> !done);
   
   // TODO: check to make sure done stays asserted indefinitely.

endmodule // bit_diff_tb_basic


// For the next testbench, we are going to start to decouple the different
// reponsibilities into separate code. First, we are going to separate the
// generator, which is responsible for generating input sequences. We generally
// want to do this with constrained-random verification, which benefits from
// having a class that acts as a basic transaction object that represents an
// abstract version of the input.
//
// One common source of confusion is how the generator and driver are different.
// In all the simple testbenches, they really weren't different. Every
// transaction object was just the set of input signals. As we get more abstract
// the transaction object starts to become much simpler.
//
// For the bit difference example, the simplest transacation we could have is
// simply the value of the data we want to test. The generator will generate
// sequences to test (without any consideration of the timing or interface
// protocol), and then the driver will convert each transaction into the
// corresponding set of inputs of the DUT pins.

class bit_diff_item1 #(WIDTH);
   rand bit [WIDTH-1:0] data;
endclass


// This initial generator simply uses CRV to create input sequences, while
// communicating with the driver.
//
// Like modules, classes can also have parameters. In this case, the generator
// has a num_tests parameter which control the number of tests generated.

class generator1 #(int NUM_TESTS, int WIDTH);

   // Mailboxes are simply queues that allow different tasks to pass data
   // between them.
   mailbox driver_mailbox;

   // Custom events can be used to synchronize tasks. Here we have events
   // that will represent the completion of the driver and generator.
   event   driver_done_event;
   event   generator_done_event;

   // Our generator uses a run method/task that produces the specified number
   // of random inputs.
   task run();
      // Create a new transaction object.
      bit_diff_item1 #(WIDTH) item = new;

      // Perform num_tests tests. 
      for (int i=0; i < NUM_TESTS; i++) begin
	 // Use the CRV randomize functionality to generate a random inpu.
	 if (!item.randomize()) $display("Randomize failed");

	 // Print a message so we know what is going on at what time.
	 $display("Time %0t [Generator]: Generating input h%h for test %0d.", $time, item.data, i);

	 // Send the random input to the driver.
	 driver_mailbox.put(item);

	 // Wait on the custom event for the driver to finish driving the 
	 // generated test before starting a new test.
	 @(driver_done_event);	 
      end

      // Report completion and trigger the generator done event for anything
      // waiting on the generator to finish.
      $display("Time %0t [Generator]: Generator done.", $time);
      -> generator_done_event;      
   endtask
endclass // generator


// Our initial driver will be very simple also. It will wait until it gets
// an input to drive, assert the appropriate signals and wait for the test
// to complete, then signal the generator to provide another test.

class driver1 #(WIDTH);   
   logic 	     clk, rst, go, done;
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   // Again, we have the same mailbox and event used in the generator. These
   // actually aren't the same yet, they are just handles to some mailbox that
   // hasn't been assigned yet. When we create the mailbox somewhere
   // else, we will initialize these handles to use the same mailbox
   // instance. The event is handled similarly.
   mailbox driver_mailbox;
   event   driver_done_event;

   task run();
      $display("Time %0t [Driver]: Driver starting.", $time);

      forever begin	 
	 bit_diff_item1 #(WIDTH) item; 

	 // Wait for the generator to send an input test transaction to drive.
	 driver_mailbox.get(item);

	 // Print a message when we get the transaction.
	 $display("Time %0t [Driver]: Driving h%h test.", $time, item.data);

	 // Drive the test by putting the data on the correpsonding input and
	 // then asserting go
	 data <= item.data;
	 go <= 1'b1;	
	 @(posedge clk);
	 go <= 1'b0;
	 	 
	 // Wait for done to be cleared and then asserted on a rising edge.
	 //@(posedge done);	 
	 @(posedge clk iff (done == 1'b0));	 
	 @(posedge clk iff (done == 1'b1));

	 // Trigger the driver done event so the generator knows to produce 
	 // another test.	 
	 ->driver_done_event;	 	 	 
      end              
   endtask       
endclass


// Module: bit_diff_tb1
// Description: In this testbench, we separate the generator and driver from
// the main testbench module.

module bit_diff_tb1;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 16;  

   logic 	     clk, rst, go, done;   
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   int 					passed, failed, reference;

   // We have to first dynamically allocate the mailbox for it to exist.
   // The mailbox variable is just a handle, which is initially untinitialized.
   mailbox driver_mailbox = new;

   // Create the events. These are static objects and don't need to be
   // dynamically allocated with new.
   event   driver_done_event;
   event   generator_done_event;

   // Create an instance of the generator and driver. Like the mailbox, any
   // class instance must be dynamically allocated with new. The variable is
   // just a handle.
   generator1 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) gen = new;
   driver1 #(.WIDTH(WIDTH)) drv = new;
   
   bit_diff DUT (.*);

   // Connect the variables in the driver to the variables in this testbench.
   // This apparently can't be done with continuous assignment.
   // NOTE: There is a much better way of doing this that we will see in the 
   // next testbench.
   always @(drv.go) go = drv.go;
   always @(drv.data) data = drv.data;
   always @(clk) drv.clk = clk;
   always @(done) drv.done = done;
  
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");

      // Initialize the generator and driver mailboxes and events.
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;
      gen.generator_done_event = generator_done_event;

      // Initialize the circuit. This could potentially be done in the driver.
      rst = 1'b1;
      go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;
      @(posedge clk);

      // Fork off two parallel tasts for the generator and the driver.
      fork
	 gen.run();
	 drv.run();	
      join_any

      // join_any blocks until any the tasks in the fork complete. We could also
      // just do a join, but in this case the driver and generator end together.
   end

   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction

   // Here we have started to separate the monitor and scoreboard from the
   // main testbench by moving it into a separate test block.
   // The forever is similar to an initial block, but repeated executes forever.
   // If we knew that the done signal couldn't have glitches, we could have
   // replaced the first 3 lines with "always @(posedge done) begin".
   always begin
      // Wait for completion.
      @(posedge clk iff (done == 1'b0));	 
      @(posedge clk iff (done == 1'b1));

      // Compare with the reference model.
      reference = model(data, WIDTH);	 
      if (result == reference) begin	 
	 $display("Test passed (time %0t) for input = h%h", $time, data);
	 passed ++;
      end
      else begin
	 $display("Test failed (time %0t): result = %0d instead of %0d for input = %h.", $time, result, reference, data);
	 failed ++;	    
      end      
   end

   // Cleanup: wait until the generator is done, then print a final summary
   // message and disable the clock generation to end the simulation.
   // Note that this only works because the generator waits on the driver,
   // which waits for completion of each test it drives. In general, it is
   // better to explicitly wait until all tests have completed.
   initial begin     
      @(generator_done_event);
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
      disable generate_clock;      
   end
   
   assert property (@(posedge clk) disable iff (rst) go && done |=> !done);
      
endmodule


// One huge weakness of the previous testbench is that we manually had to
// connect the testbench variables to the driver's variables. For this simple
// example, it wasn't a huge overhead, but a complex design could have 100s of
// signals. Clearly we wouldn't want to manually connect those.
//
// Instead, we can encapsulate all the port signal as part of an interface
// as shown below. We can now pass around this one interface instead of all
// the individual signals. Nearly every real testbench will use an interface
// like this.

interface bit_diff_if #(parameter int WIDTH) (input logic clk);
   logic 	     rst, go, done;
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;
endinterface


// Driver 2 is a simplified version of driver 1 that uses the new interface
// instead of separate signals. We don't need a new generator yet since it
// doesn't use any of the testbench signals, which illustrates one advantage
// of this decoupling based on separate responsibilities.

class driver2 #(WIDTH);
   // We don't want the actual interface here, just a pointer to it, which
   // we accomplish with the virtual keyword.   
   virtual 	     bit_diff_if #(.WIDTH(WIDTH)) vif;   
   
   mailbox 	     driver_mailbox;
   event 	     driver_done_event;

   task run();
      $display("Time %0t [Driver]: Driver starting.", $time);

      forever begin
	 bit_diff_item1 #(WIDTH) item; 

	 // Wait for the generator to send an input test to drive.
	 driver_mailbox.get(item);		 
	 $display("Time %0t [Driver]: Driving h%h test.", $time, item.data);

	 // We can now access all the variable through the interface.
	 vif.data <= item.data;
	 vif.go <= 1'b1;
	 @(posedge vif.clk);	
	 vif.go <= 1'b0;	 	 
	 @(posedge vif.clk iff (vif.done == 1'b0));	 
	 @(posedge vif.clk iff (vif.done == 1'b1));
	 -> driver_done_event;	 	 	 
      end              
   endtask       
endclass
 

// Module: bit_diff_tb2
// Description: This testbench simplifies the previous one by using the
// new interface.

module bit_diff_tb2;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 16;  

   // We only need the clk signal now since everything else will be
   // part of the interface.
   logic 	     clk;   
   int 		     passed, failed, reference;
   
   // We have to first dynamically allocate the mailbox for it to exist.
   // The mailbox variable is just a handle, which is initially untinitialized.
   mailbox driver_mailbox = new;

   // Create the events. These are static objects and don't need to be
   // dynamically allocated with new.
   event   driver_done_event;
   event   generator_done_event;

   // Create an instance of the generator and driver. Like the mailbox, any
   // class instance must be dynamically allocated with new. The variable is
   // just a handle.
   generator1 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) gen = new;
   driver2 #(.WIDTH(WIDTH)) drv = new;

   // Create the interface.
   bit_diff_if #(.WIDTH(WIDTH))_if (.clk(clk));

   // Instantiate the DUT. We unfortunately can't use .* anymore because
   // of the interface. However, we could modify the DUT module to use
   // the interface, in which case we only need to connect the interface
   // here. The tutorials will illustrate synthesizable interfaces in another
   // section.
   bit_diff DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .data(_if.data), .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin      
      $timeformat(-9, 0, " ns");

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

   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction

   // Here we have started to separate the monitor and scoreboard from the
   // main testbench by moving it into a separate test block.
   // The forever is similar to an initial block, but repeated executes forever.
   // If we knew that the done signal couldn't have glitches, we could have
   // replaced the first 3 lines with "always @(posedge done) begin".
   always begin
      // Wait for completion.
      @(posedge clk iff (_if.done == 1'b0));	 
      @(posedge clk iff (_if.done == 1'b1));

      // Compare with the reference model.
      reference = model(_if.data, WIDTH);	 
      if (_if.result == reference) begin	 
	 $display("Test passed (time %0t) for input = h%h", $time, _if.data);
	 passed ++;
      end
      else begin
	 $display("Test failed (time %0t): result = %0d instead of %0d for input = h%h.", $time, _if.result, reference, _if.data);
	 failed ++;	    
      end            
   end

   initial begin     
      @(generator_done_event);
      $display("Tests completed: %0d passed, %0d failed", passed, failed);
      disable generate_clock;      
   end
   
   assert property (@(posedge clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
     
endmodule // bit_diff_tb2


// Next, we modify the testbench further by decoupling the monitor and
// scoreboard from the main testbench code.
//
// To separate the monitor and scoreboard, we need to extend our transaction
// object to include the result, which the monitor sends to the scoreboard.
//
// Notice that the result is not rand because it is provided as a DUT output.

class bit_diff_item2 #(WIDTH);
   rand bit [WIDTH-1:0] data;
   bit signed [$clog2(WIDTH*2+1)-1:0] result;
endclass

// The monitor simply monitors the outputs of the DUT and looks for any
// situation we want to verify. Since we only have one output for this example,
// the monitor simply wait until completion and then passes the result output
// to the scoreboard.

class monitor1 #(parameter int WIDTH);
   // Like the driver and generator, we encapsulate all the DUT signals in an
   // interface.
   virtual 	     bit_diff_if #(.WIDTH(WIDTH)) vif;

   // Mailbox handle for sending results to the scoreboard for verification.
   mailbox 	     scoreboard_mailbox;
   
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
	 // Create the transaction object.
	 bit_diff_item2 #(.WIDTH(WIDTH)) item = new;

	 // Wait for completion.
	 @(posedge vif.clk iff (vif.done == 1'b0));	 
	 @(posedge vif.clk iff (vif.done == 1'b1));

	 // Save the input data and result from the interface.
	 item.data = vif.data;
	 item.result = vif.result;
	 $display("Time %0t [Monitor]: Monitor detected result=%0d for data=h%h.", $time, vif.result, vif.data);

	 // Send the input data and result to the scoreboard and go back to
	 // monitoring.
	 scoreboard_mailbox.put(item);
      end
   endtask       
endclass


// The scoreboard waits for a transaction from the  monitor, which specifies 
// the input being tested and the corresponding result. The scoreboard then
// compares the result with the reference model, updates statistics, and
// prints loggin information.

class scoreboard1 #(parameter int WIDTH);
   // Mailbox handle to receive data from the monitor.
   mailbox scoreboard_mailbox;  
   int 	   passed, failed, reference;

   // We move the reference model into the scoreboard here, since it isn't
   // needed anywhere else.
   function int model(int data, int width);
      automatic int 		     diff = 0;
      
      for (int i=0; i < WIDTH; i++) begin
	 diff = data[0] ? diff+1  : diff-1;
	 data = data >> 1;	 
      end
      
      return diff;      
   endfunction

   task run();
      passed = 0;
      failed = 0;
            
      forever begin
	 bit_diff_item2 #(.WIDTH(WIDTH)) item;
	 
	 // Wait until the monitor sends a result to verify.
	 scoreboard_mailbox.get(item);

	 // Verify the result.
	 reference = model(item.data, WIDTH);	 
	 if (item.result == reference) begin
	    $display("Time %0t [Scoreboard] Test passed for input = h%h", $time, item.data);
	    passed ++;
	 end
	 else begin
	    $display("Time %0t [Scoreboard] Test failed: result = %0d instead of %0d for input = h%h.", $time, item.result, reference, item.data);
	    failed ++;	    
	 end
      end
   endtask

   // Method to report the status of the simulation at any point.
   function void report_status();     
      $display("Test status: %0d passed, %0d failed", passed, failed);
   endfunction      
endclass


// Module: bit_diff_tb3
// Description: Modified version of the previous testbench to decouple the
// monitor and scoreboard. Notice that the main testbench module keeps getting
// simpler because the different reponsibilities are moved elsewhere/

module bit_diff_tb3;
   
   localparam NUM_TESTS = 1000;
   localparam WIDTH = 16;
   
   logic 	     clk;
  
   mailbox 	     driver_mailbox = new;
   mailbox 	     scoreboard_mailbox = new;
   event 	     driver_done_event;
   event 	     generator_done_event;
   generator1 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) gen = new;
   driver2  #(.WIDTH(WIDTH)) drv = new;
   monitor1 #(.WIDTH(WIDTH)) monitor = new;
   scoreboard1 #(.WIDTH(WIDTH)) scoreboard  = new;
   
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
		 .done(_if.done), .data(_if.data), .result(_if.result));
   
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

      // Initialize the monitor and scoreboard.
      monitor.vif = _if;
      monitor.scoreboard_mailbox = scoreboard_mailbox;
      scoreboard.scoreboard_mailbox = scoreboard_mailbox;      

      // Initialize the circuit.
      _if.rst = 1'b1;
      _if.go = 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      _if.rst = 1'b0;
      @(posedge clk);

      // Fork off threads for the other main components.
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

   assert property (@(posedge clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
     
endmodule // bit_diff_tb3

/*

class env #(int num_tests);

   generator1 #(.num_tests(num_tests)) gen;
   driver2 drv;
   monitor1 monitor;
   scoreboard1 scoreboard;
   virtual bit_diff_if vif;
   
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


module bit_diff_tb4;
   
   localparam NUM_TESTS = 100;
   logic 	     clk;
   env #(.num_tests(NUM_TESTS)) _env = new;
   
   bit_diff_if _if (.clk(clk));   
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
     
endmodule // bit_diff_tb4


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
   virtual 	     bit_diff_if vif;
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
   virtual 	     bit_diff_if vif;
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
   
   function int model(int n);
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
	 reference = model(final_item.n);	 
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
   virtual bit_diff_if vif;
   
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


module bit_diff_tb5;
   
   localparam NUM_TESTS = 1000;
   logic 	     clk;
   env2 #(.num_tests(NUM_TESTS)) _env = new;
   
   bit_diff_if _if (.clk(clk));   
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
     
endmodule // bit_diff_tb5


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
   virtual 	     bit_diff_if vif;
   mailbox 	     driver_mailbox;
   mailbox 	     scoreboard_n_mailbox;
   event 	     driver_done_event;

   function new(virtual bit_diff_if _vif, mailbox _driver_mailbox, 
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
   virtual 	     bit_diff_if vif;
   mailbox 	     scoreboard_result_mailbox;

   function new(virtual bit_diff_if _vif, mailbox _scoreboard_result_mailbox);
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
   
   function int model(int n);
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
	 reference = model(final_item.n);	 
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
      $display("%0d total tests: %0d passed, %0d failed", passed+failed, passed, failed);
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
      
   function new(virtual bit_diff_if vif);      
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


module bit_diff_tb6;
   
   localparam NUM_TESTS = 1000;
   logic 	     clk;
   
   bit_diff_if _if (.clk(clk));   
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
     
endmodule // bit_diff_tb6


class generator4 #(bit use_consecutive_inputs=1'b0);
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      fib_item3 item = new;
      bit [4:0] n = '0;
                        
      forever begin
	 if (!use_consecutive_inputs) begin
	    if (!item.randomize()) $display("Randomize failed");
	    //$display("Time %0t [Generator]: Generating fib input %0d, go=%0b.", $time, item.n, item.go); 
	 end
	 else begin
	    item.n = n;
	    n ++;	    
	 end
	 driver_mailbox.put(item);
	 @(driver_done_event);
      end
   endtask
endclass // generator3


class driver5 #(use_one_test_at_a_time=1'b0);   
   virtual 	     bit_diff_if vif;
   mailbox 	     driver_mailbox;
   mailbox 	     scoreboard_n_mailbox;
   event 	     driver_done_event;

   function new(virtual bit_diff_if _vif, mailbox _driver_mailbox, 
		mailbox _scoreboard_n_mailbox, event _driver_done_event);
      vif = _vif;      
      driver_mailbox = _driver_mailbox;
      scoreboard_n_mailbox = _scoreboard_n_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      fib_item3 item;

      if (use_one_test_at_a_time) begin
	 forever begin
	    driver_mailbox.get(item);
	    vif.n = item.n;
	    vif.go = 1'b1;
	    scoreboard_n_mailbox.put(item);
	    @(posedge vif.done);
	    vif.go = 1'b0;
	    @(posedge vif.clk);
	    -> driver_done_event;	    
	 end
      end
      else begin      
	 logic is_first_test = 1'b1;      
	 logic is_active = 1'b0;
	 $display("Time %0t [Driver]: Driver starting.", $time);
         
	 forever begin	    
	    //@(posedge vif.clk);
	    
	    // If the circuit is reset at any point, reset the driver state.
	    while (vif.rst) begin
	       @(posedge vif.clk);	  
	       is_first_test = 1'b1;
	       is_active = 1'b0;	    	    
	    end
	    
	    driver_mailbox.get(item);
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
      end
   endtask       
endclass // driver5


class env4 #(int num_tests, bit use_consecutive_inputs=1'b0,
	     bit use_one_test_at_a_time=1'b0 );

   generator4 #(use_consecutive_inputs) gen;
   driver5 #(use_one_test_at_a_time) drv;
   monitor3 monitor;
   scoreboard3 #(.num_tests(num_tests)) scoreboard;
   
   mailbox scoreboard_n_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
      
   function new(virtual bit_diff_if vif);      
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

   function void report_status();
      scoreboard.report_status();
   endfunction
   
   virtual 	     task run();      
      fork
	 gen.run();
	 drv.run();
	 monitor.run();
	 scoreboard.run();	 
      join_any

      disable fork;      
   endtask // run   
endclass // env4


class test #(string name="default_test_name", int num_tests, bit use_consecutive_inputs=1'b0,
	     bit use_one_test_at_a_time=1'b0, int repeats=0 );

   virtual 	 bit_diff_if vif;
   env4 #(num_tests, use_consecutive_inputs, use_one_test_at_a_time) e;
   
   function new(virtual bit_diff_if _vif);
      vif = _vif;      
   endfunction // new

   function void report_status();
      $display("Results for Test %0s", name);      
      e.report_status();
   endfunction
   
   task run();
      $display("Time %0t [Test]: Starting test.", $time);      
      for (int i=0; i < repeats+1; i++) begin
	 e = new(vif);      
	 vif.rst = 1'b1;
	 vif.go = 1'b0;      
	 for (int i=0; i < 5; i++) @(posedge vif.clk);
	 vif.rst = 1'b0;
	 @(posedge vif.clk);
	 e.run();
	 @(posedge vif.clk);     
      end
      $display("Time %0t [Test]: Test completed.", $time);      
   endtask   
endclass // test


module bit_diff_tb7;
   
   localparam NUM_TESTS = 1000;
   logic 	     clk;
   
   bit_diff_if _if (.clk(clk));   
   fib DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
	    .done(_if.done), .n(_if.n), .result(_if.result));

   test #(.name("Random Test"), .num_tests(1000)) test0 = new(_if);
   test #(.name("Consecutive Test"), .num_tests(200), .use_consecutive_inputs(1'b1), .use_one_test_at_a_time(1'b1)) test1 = new(_if);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin      
      $timeformat(-9, 0, " ns");
      test0.run();      
      test1.run();
      test0.report_status();
      test1.report_status();      
      disable generate_clock;      
   end
      
   assert property (@(posedge _if.clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
     
endmodule // bit_diff_tb7
*/
