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
   
   logic             clk, rst, go, done;  
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   // Testbench variables
   int                                  passed, failed, reference;

   // Instantiate the DUT
   bit_diff #(.WIDTH(WIDTH)) DUT (.*);

   // Reference model for getting the correct result.
   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
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
      rst <= 1'b1;
      go <= 1'b0;
      data <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      // Perform NUM_TESTS number of randome tests.
      for (int i=0; i < NUM_TESTS; i++) begin
         data <= $random;
         go <= 1'b1;
         @(posedge clk);
         go <= 1'b0;
         
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

   // Check to make sure done cleared within a cycle. Go is anded with done
   // because go should have no effect when the circuit is already active.
   assert property (@(posedge clk) disable iff (rst) go && done |=> !done);
   
   // Check to make sure done is only cleared when go is asserted (i.e. done is
   // left asserted indefinitely).
   assert property (@(posedge clk) disable iff (rst) $fell(done) |-> $past(go,1));
   
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
// For the bit difference example, the simplest transaction we could have is
// the value of the data we want to test. The generator will generate
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


// Our initial driver will also be very simple. It will wait until it gets
// an input to drive, assert the appropriate signals and wait for the test
// to complete, then signal the generator to provide another test.

class driver1 #(WIDTH);   
   logic             clk, rst, go, done;
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
         -> driver_done_event;                    
      end              
   endtask       
endclass


// Module: bit_diff_tb1
// Description: In this testbench, we separate the generator and driver from
// the main testbench module.

module bit_diff_tb1;

   localparam NUM_TESTS = 1000;   
   localparam WIDTH = 16;  

   logic             clk, rst, go, done;   
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   int                                  passed, failed, reference;

   // We have to first dynamically allocate the mailbox for it to exist.
   // The mailbox variable is just a handle, which is initially uninitialized.
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

   bit_diff #(.WIDTH(WIDTH)) DUT (.*);
   
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
      rst <= 1'b1;
      go <= 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);

      // Fork off two parallel tasts for the generator and the driver.
      fork
         gen.run();
         drv.run();     
      join_any

      // join_any blocks until any the tasks in the fork complete. We could also
      // potentially do a join, but that wouldn't work in this case since the 
      // driver runs forever.
   end

   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
         diff = data[0] ? diff+1  : diff-1;
         data = data >> 1;       
      end
      
      return diff;      
   endfunction

   // Here we have started to separate the monitor and scoreboard from the
   // main testbench by moving it into a separate test block. 
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
   assert property (@(posedge clk) disable iff (rst) $fell(done) |-> $past(go,1));
      
endmodule


// One huge weakness of the previous testbench is that we manually had to
// connect the testbench variables to the driver's variables. For this simple
// example, it wasn't a huge overhead, but a complex design could have 100s of
// signals. Clearly we wouldn't want to manually connect those.
//
// Instead, we can encapsulate all the port signals as part of an interface
// as shown below. We can now pass around this one interface instead of all
// the individual signals. Nearly every real testbench will use an interface
// like this.

interface bit_diff_if #(parameter int WIDTH) (input logic clk);
   logic             rst, go, done;
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
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;   
   
   mailbox           driver_mailbox;
   event             driver_done_event;

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
   logic             clk;   
   int               passed, failed, reference;
   
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
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));

   // Instantiate the DUT. We unfortunately can't use .* anymore because
   // of the interface. However, we could modify the DUT module to use
   // the interface, in which case we only need to connect the interface
   // here. The tutorials will illustrate synthesizable interfaces in another
   // section.
   bit_diff #(.WIDTH(WIDTH)) DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
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
            
      _if.rst <= 1'b1;
      _if.go <= 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      _if.rst <= 1'b0;
      @(posedge clk);
      fork
         gen.run();
         drv.run();
      join_any
   end

   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
         diff = data[0] ? diff+1  : diff-1;
         data = data >> 1;       
      end
      
      return diff;      
   endfunction

   // Same as previous testbench, except now it uses the interface.
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
   assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));     
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
// the monitor simply waits until completion and then passes the result output
// to the scoreboard.

class monitor1 #(parameter int WIDTH);
   // Like the driver and generator, we encapsulate all the DUT signals in an
   // interface.
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;

   // Mailbox handle for sending results to the scoreboard for verification.
   mailbox           scoreboard_mailbox;
   
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


// The scoreboard waits for a transaction from the monitor, which specifies 
// the input being tested and the corresponding result. The scoreboard then
// compares the result with the reference model, updates statistics, and
// prints logging information.

class scoreboard1 #(parameter int WIDTH);
   // Mailbox handle to receive data from the monitor.
   mailbox scoreboard_mailbox;  
   int     passed, failed, reference;

   // We move the reference model into the scoreboard here, since it isn't
   // needed anywhere else.
   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
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
// simpler because the different reponsibilities are moved elsewhere

module bit_diff_tb3;
   
   localparam NUM_TESTS = 1000;
   localparam WIDTH = 16;
   
   logic             clk;
  
   mailbox           driver_mailbox = new;
   mailbox           scoreboard_mailbox = new;
   event             driver_done_event;
   event             generator_done_event;
   generator1 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) gen = new;
   driver2  #(.WIDTH(WIDTH)) drv = new;
   monitor1 #(.WIDTH(WIDTH)) monitor = new;
   scoreboard1 #(.WIDTH(WIDTH)) scoreboard  = new;
   
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff #(.WIDTH(WIDTH)) DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
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
      _if.rst <= 1'b1;
      _if.go <= 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      _if.rst <= 1'b0;
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
   assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));     
     
endmodule // bit_diff_tb3


// One common testbench strategy is to encapsulate the generator, driver,
// monitor, and scoreboard inside an "environment," which further simplifies
// the main testbench.
//
// Here we create an initial environment which does this. It basically replaces
// the code from the main testbench that declares, instantiates, and connects 
// everything together.

class env #(int NUM_TESTS, int WIDTH);

   generator1 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) gen;
   driver2  #(.WIDTH(WIDTH)) drv;
   monitor1 #(.WIDTH(WIDTH)) monitor;
   scoreboard1 #(.WIDTH(WIDTH)) scoreboard;
   
   virtual bit_diff_if #(.WIDTH(WIDTH)) vif;
   
   mailbox scoreboard_mailbox;
   mailbox driver_mailbox;
   
   event             driver_done_event;
   event             generator_done_event;

   // We give the environment a new method to create new instances of everything
   // encapsulated by the environment.
   function new();
      gen = new;
      drv = new;
      monitor = new;
      scoreboard = new;
      scoreboard_mailbox = new;
      driver_mailbox = new;
   endfunction // new

   // The environment's run task connects everything together and forks off
   // the individual threads. The connections could have also been made in the
   // new() method, but we need the fork code here.    
   virtual           task run();
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

      // When any of the tasks complete, report the status of the tests. While
      // it might be confusing to wait for any of the tasks to complete, 
      // instead of waiting for all tasks, the generator is the only task that 
      // actually ever exits, which it does after all the tests have completed.
      scoreboard.report_status();      
   endtask // run   
endclass


// Module: bit_diff_tb4
// Description: This testbench simplifies the previous one by using the newly
// created environment. As before, this main testbench gets even simpler with
// the environment.

module bit_diff_tb4;
   
   localparam NUM_TESTS = 1000;
   localparam WIDTH = 16;
   
   logic             clk;

   // Instead of separately creating the generator, driver, monitor, and 
   // scoreboard, we just create the environment.
   env #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) _env = new;
   
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff #(.WIDTH(WIDTH)) DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
                                  .done(_if.done), .data(_if.data), 
                                  .result(_if.result));
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   initial begin      
      $timeformat(-9, 0, " ns");

      // Connect the interface to the environment.
      _env.vif = _if;

      // Initialize the circuit.
      _if.rst <= 1'b1;
      _if.go <= 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      _if.rst <= 1'b0;
      @(posedge clk);

      // Run the environment.
      _env.run();
      disable generate_clock;      
   end
         
   assert property (@(posedge _if.clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
   assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));
     
endmodule // bit_diff_tb4


// Up to this point, the actual coverage is pretty weak. The generator simply
// generates a test and then waits until that test is done. This done not test
// modifying the data input while a test is ongoing. It also doesn't test 
// toggling go while a test is ongoing.
//
// We now start to improve the testbench by adding these capabilities to the
// generator. The generator is now responsible for generating values for the
// data input and the go input, and it no longer waits for the driver to
// finish the previous test.
//
// To support this new functionality, we need to expand our transaction object
// with a go bit.

class bit_diff_item3 #(WIDTH);
   rand bit [WIDTH-1:0] data;
   rand bit go;   
   bit signed [$clog2(WIDTH*2+1)-1:0] result;

   // A uniform distribution of go values probably isn't what we want, so
   // we'll make sure go is 1'b0 90% of the time.
   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass


// In the new generator, we make several changes. First, we use the new
// transaction object to random produce go values. Second, we remove the for
// loop. In this new version, the testbench won't wait for the generator to
// finish. It will wait for the scoreboard to finish. Not only is this more
// a intuitive way of waiting for completion, but it is also necessary.
// Previously, the generator produced one data input per execution of the DUT.
// Now, the generator produces input values as frequently as it can. Many of
// those values will occur when the DUT is already active. So, if we simply
// counted the number of inputs tested, the number of actual executions of the
// DUT would be much smaller than before.

class generator2 #(int WIDTH);
   mailbox driver_mailbox;
   event   driver_done_event;
  
   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) item;

      forever begin
         item = new;     
         if (!item.randomize()) $display("Randomize failed");

         // This display is commented out because this loop can potentially
         // execute every cycle, which could make the log overwhelming.
         //$display("Time %0t [Generator]: Generating input h%h, go=%0b.", $time, item.data, item.go);

         driver_mailbox.put(item);

         // The generator still waits for the driver to finish driving the
         // current test, but we'll see that happens every cycle now, instead
         // of the driver waiting for completion of the DUT.
         @(driver_done_event);
      end
   endtask
endclass // generator2


// The new driver is more complicated because it no longer just has to wait
// for a message from the generator. It still drives tests from the generator,
// but since some of those tests will not actually produce an output from the
// DUT, the driver must keep track of which inputs will affect the output.
// For example, data inputs that don't coincide with assertions of go should
// be ignored by the scoreboard. Similarly, assertions of go while the DUT
// is already active should also be ignored by the scoreboard.
//
// We could potentially move this code to the monitor, in which case the monitor
// would have to check the DUT inputs and outputs.

class driver3 #(int WIDTH);
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;
   mailbox           driver_mailbox;

   // Since only the driver knows when an input can cause the DUT to start a
   // new execution, we create a new scoreboard mailbox that the driver will
   // use to send data inputs that will produce an output from the DUT.
   mailbox           scoreboard_data_mailbox;
   event             driver_done_event;

   task run();
      // To know whether or not generated inputs will create a DUT output, 
      // we need to know whether or not the DUT is currently active.
      logic is_first_test = 1'b1;      
      logic is_active = 1'b0;
      $display("Time %0t [Driver]: Driver starting.", $time);
            
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item;
         
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
         //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);
         
         // For this driver, we drive both the data and go inputs directly 
         // from the generator.
         vif.data = item.data;
         vif.go = item.go;

         // Wait until the next clock edge where the inputs will be seen.
         // This is needed here because signals haven't changed yet on the
         // current clock cycle. So, if done is about to change, we won't see
         // it. That would cause the following code to mistake the DUT as
         // being active, which could prevent sending the test to the
         // scoreboard.
         @(posedge vif.clk);
                 
         // If done is asserted, or if this is the first_test, 
         // then the DUT should be inactive and ready for another test.  
         if (vif.done || is_first_test)
           is_active = 1'b0;
                                 
         // If the DUT isn't already active, and we get a go signal, we are
         // starting a test, so inform the scoreboard. The scoreboard will
         // then wait to get the result from the monitor. This strategy allows
         // the testbench to test assertions of go that don't correspond to
         // the start of a test because the DUT is already active. The DUT
         // should ignore these assertions.
         if (!is_active && vif.go) begin            
            $display("Time %0t [Driver]: Sending start of test for data=h%h.", $time, item.data);
            scoreboard_data_mailbox.put(item);
            is_active = 1'b1;       
            is_first_test = 1'b0;
         end

         // Tell the generator the driver has driven the last test, which
         // happens every cycle except during reset.
         -> driver_done_event;   
      end              
   endtask       
endclass


// The monitor becomes a little simpler now because the driver informs the
// scoreboard of the corresponding input for the next output. So, the monitor
// solely send the output to the scoreboard.

class monitor2 #(int WIDTH);
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;

   // We rename the scoreboard mailbox since driver now uses a separate
   // mailbox for sending data inputs.
   mailbox           scoreboard_result_mailbox;

   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item = new;
         @(posedge vif.clk iff (vif.done == 1'b0));      
         @(posedge vif.clk iff (vif.done == 1'b1));      
         // In this version, we only care about the result, because the driver
         // already informed the scoreboard of the next n value to check.
         item.result = vif.result;
         $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, vif.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


// With the new scoreboard, we count the number of tests here instead of in
// the generator.

class scoreboard2 #(int NUM_TESTS, int WIDTH);
   // The scoreboard has two separate mailboxes now: one for the data input
   // from the driver, and a second for the result output from the monitor.
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_data_mailbox;
   int     passed, failed, reference;

   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
         diff = data[0] ? diff+1  : diff-1;
         data = data >> 1;       
      end
      
      return diff;      
   endfunction

   task run();
      passed = 0;
      failed = 0;

      for (int i=0; i < NUM_TESTS; i++) begin
         
         bit_diff_item3 #(.WIDTH(WIDTH)) in_item;       
         bit_diff_item3 #(.WIDTH(WIDTH)) out_item;       
        
         // First wait until the driver informs us of a new test.
         scoreboard_data_mailbox.get(in_item);
         $display("Time %0t [Scoreboard]: Received start of test for data=h%h.", $time, in_item.data);

         // Then, wait until the monitor tells us that test is complete.
         scoreboard_result_mailbox.get(out_item);
         $display("Time %0t [Scoreboard]: Received result=%0d for data=h%h.", $time, out_item.result, in_item.data);

         // Get the correct result based on the input at the start of the test.
         reference = model(in_item.data, WIDTH);         
         if (out_item.result == reference) begin
            $display("Time %0t [Scoreboard] Test passed for data=h%h", $time, in_item.data);
            passed ++;
         end
         else begin
            $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for data = h%h.", $time, out_item.result, reference, in_item.data);
            failed ++;      
         end
      end
   endtask

   function void report_status();     
      $display("Test status: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass // scoreboard2


// The new environment only changes to use the new classes.

class env2 #(int NUM_TESTS, int WIDTH);

   generator2 #(.WIDTH(WIDTH)) gen;
   driver3  #(.WIDTH(WIDTH)) drv;
   monitor2 #(.WIDTH(WIDTH)) monitor;
   scoreboard2 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) scoreboard;
   
   virtual bit_diff_if #(.WIDTH(WIDTH)) vif;

   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
      
   function new();
      gen = new;
      drv = new;
      monitor = new;
      scoreboard = new;
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
   endfunction // new

   virtual           task run();
      drv.vif = vif;
      monitor.vif = vif;
      
      gen.driver_mailbox = driver_mailbox;
      drv.driver_mailbox = driver_mailbox;
      
      drv.scoreboard_data_mailbox = scoreboard_data_mailbox;
      scoreboard.scoreboard_data_mailbox = scoreboard_data_mailbox;
      
      monitor.scoreboard_result_mailbox = scoreboard_result_mailbox;
      scoreboard.scoreboard_result_mailbox = scoreboard_result_mailbox;
   
      gen.driver_done_event = driver_done_event;
      drv.driver_done_event = driver_done_event;

      // In this new environment, the fork exits when the scoreboard finishes
      // all tests.         
      fork
         gen.run();
         drv.run();
         monitor.run();
         scoreboard.run();       
      join_any

      scoreboard.report_status();      
   endtask 
endclass


// Module: bit_diff_tb5
// Description: Simply updates the previous testbench to use the new
// environment. Notice how significant changes can be made to other parts
// without requiring any changes here.

module bit_diff_tb5;
   
   localparam NUM_TESTS = 1000;
   localparam WIDTH = 16;
   
   logic             clk;
   env2 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) _env = new;
   
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
            .done(_if.done), .data(_if.data), .result(_if.result));
   
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


// The above style is common, but there is a safer way to construct class
// objects. In object-oriented programming, one strategy is to make sure
// that an object is fully initialized after being constructed. This way the
// user of the object doesn't have to do anything else before using it.
//
// In the previous examples, class object were constructed with no parameters.
// All of the class variables were then initialized externally. In general,
// I recommend against this strategy. Instead, I prefer to add parameters
// to the new method that establish all connections. Then, after calling new
// I know the object is in a safe state and doesn't require further
// initialization.

// In the following generator, we transform the previous generator to establish
// all the connections within the new method.
 
class generator3 #(int WIDTH);
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) item;

      forever begin
         item = new;     
         if (!item.randomize()) $display("Randomize failed");
         //$display("Time %0t [Generator]: Generating input h%h, go=%0b.", $time, item.data, item.go);

         driver_mailbox.put(item);
         @(driver_done_event);
      end
   endtask
endclass // generator3


// A new driver class with the similar style of constructor.

class driver4 #(int WIDTH);
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;
   mailbox           driver_mailbox;
   mailbox           scoreboard_data_mailbox;
   event             driver_done_event;

   // New constructor to establish all connections.
   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) _vif, mailbox _driver_mailbox, 
                mailbox _scoreboard_data_mailbox, event _driver_done_event);
      vif = _vif;      
      driver_mailbox = _driver_mailbox;
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      // To know whether or not generated inputs will create a DUT output, 
      // we need to know whether or not the DUT is currently active.
      logic is_first_test = 1'b1;      
      logic is_active = 1'b0;
      $display("Time %0t [Driver]: Driver starting.", $time);
            
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item;
         
         // If the circuit is reset at any point, reset the driver state.
         while (vif.rst) begin
            @(posedge vif.clk);   
            is_first_test = 1'b1;
            is_active = 1'b0;               
         end
         
         driver_mailbox.get(item);
         //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);
         
         vif.data = item.data;
         vif.go = item.go;
         @(posedge vif.clk);
                 
         // If done is asserted, or if this is the first_test, 
         // then the DUT should be inactive and ready for another test.  
         if (vif.done || is_first_test)
           is_active = 1'b0;
                                 
         // If the DUT isn't already active, and we get a go signal, we are
         // starting a test, so inform the scoreboard. The scoreboard will
         // then wait to get the result from the monitor.        
         if (!is_active && vif.go) begin            
            $display("Time %0t [Driver]: Sending start of test for data=h%h.", $time, item.data);
            scoreboard_data_mailbox.put(item);
            is_active = 1'b1;       
            is_first_test = 1'b0;
         end

         -> driver_done_event;   
      end              
   endtask       
endclass


// The new monitor adds the same type of constructor.

class monitor3 #(int WIDTH);
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;
   mailbox           scoreboard_result_mailbox;

   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) _vif, mailbox _scoreboard_result_mailbox);
      vif = _vif;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
   
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item = new;
         @(posedge vif.clk iff (vif.done == 1'b0));      
         @(posedge vif.clk iff (vif.done == 1'b1));      
         item.result = vif.result;
         $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, vif.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


// Here, we add the new constuctor to the scoreboard.

class scoreboard3 #(int NUM_TESTS, int WIDTH);
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_data_mailbox;
   int     passed, failed, reference;

   function new(mailbox _scoreboard_data_mailbox, mailbox _scoreboard_result_mailbox);
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;

      passed = 0;
      failed = 0;
   endfunction // new
   
   function int model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
         diff = data[0] ? diff+1  : diff-1;
         data = data >> 1;       
      end
      
      return diff;      
   endfunction

   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) in_item;  
      bit_diff_item3 #(.WIDTH(WIDTH)) out_item;  
      
      for (int i=0; i < NUM_TESTS; i++) begin
                
         // First wait until the driver informs us of a new test.
         scoreboard_data_mailbox.get(in_item);
         $display("Time %0t [Scoreboard]: Received start of test for data=h%h.", $time, in_item.data);

         // Then, wait until the monitor tells us that test is complete.
         scoreboard_result_mailbox.get(out_item);
         $display("Time %0t [Scoreboard]: Received result=%0d for data=h%h.", $time, out_item.result, in_item.data);

         // Get the correct result based on the input at the start of the test.
         reference = model(in_item.data, WIDTH);         
         if (out_item.result == reference) begin
            $display("Time %0t [Scoreboard] Test passed for data=h%h", $time, in_item.data);
            passed ++;
         end
         else begin
            $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for data = h%h.", $time, out_item.result, reference, in_item.data);
            failed ++;      
         end
      end // for (int i=0; i < NUM_TESTS; i++)

      
      // Remove any leftover messages that might be in the mailbox upon
      // completion. This is needed for the repeat functionality to work.
      // If data is left in the mailbox when repeating a test, that data
      // will be detected as part of the current test.
      while(scoreboard_data_mailbox.try_get(in_item));
      while(scoreboard_result_mailbox.try_get(out_item));
   endtask

   function void report_status();     
      $display("Test status: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass // scoreboard3


// A new environment class to use the update classes with new constructors.
// This illustrates the different initialization strategy. The environment
// itself has a constructor that takes the interface as a parameter.

class env3 #(int NUM_TESTS, int WIDTH);

   generator3 #(.WIDTH(WIDTH)) gen;
   driver4  #(.WIDTH(WIDTH)) drv;
   monitor3 #(.WIDTH(WIDTH)) monitor;
   scoreboard3 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) scoreboard;
   
   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) vif);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;

      // This is a much less error-prone way to create the environment. In the
      // previous version, we instaniated each of these classes and then
      // connected their internal signals within the environment. The risk
      // with that approach is that we don't get any compiler errors if we
      // forget to connect something. The errors will only show up during 
      // simulation.
      //
      // With this new approach, we only construct each instance when we have
      // all the information we need for it. In other words, every object is
      // fully initialized upon construction. If we leave out required
      // parameters from the constructor, we will get compiler errors, which is
      // what we want. Our goal is to always catch as many problems as possible
      // at compile time.
      
      gen = new(driver_mailbox, driver_done_event);
      drv = new(vif, driver_mailbox, scoreboard_data_mailbox, driver_done_event);
      monitor = new(vif, scoreboard_result_mailbox);
      scoreboard = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new

   virtual           task run();      
      fork
         gen.run();
         drv.run();
         monitor.run();
         scoreboard.run();       
      join_any

      scoreboard.report_status();      
   endtask // run   
endclass


// Module: bit_diff_tb6
// Description: Here we update the testbench to use the new environment with
// its new constructor.

module bit_diff_tb6;

   localparam NUM_TESTS = 1000;
   localparam WIDTH = 16;   
   logic             clk;
   
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
            .done(_if.done), .data(_if.data), .result(_if.result));

   // Pass the interface to the constructor so that the environment isn't
   // created in an invalid state that requires further initialization.
   env3 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) _env = new(_if);
   
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


// We now have a reasonably solid structure for a testbench. One other
// abstraction that is often used in addition to an environment is a "test."
// Think of a test as a single configuration of an environment. For example,
// in one test we might configure the environment to do a different number
// of tests, or to repeat the sequences some number of times, or to use a
// different distribution, etc. 
//
// Here we will illustrate this concept by extending the environment with 
// configuration options and then running multiple configuration (i.e. tests)
// from the testbench module.


// First, we will extend the generator with a configuration option to either
// create random inputs, or to use a sequence of consecutive input values
// (e.g., 0, 1, 2, 3, 4, etc.) with only one test running at a time. This
// specific configuration option doesn't necessarily help with coverage, but
// is useful for debugging when errors are deteched.

class generator4 #(int WIDTH, bit CONSECUTIVE_INPUTS);
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) item;

      // Start the consecutive sequence at 0. This could also be modified with
      // another configuration parameter.
      bit [WIDTH-1:0] data = '0;     
      
      forever begin
         item = new;     
         if (!CONSECUTIVE_INPUTS) begin
            if (!item.randomize()) $display("Randomize failed");
            //$display("Time %0t [Generator]: Generating input h%h, go=%0b.", $time, item.data, item.go); 
         end
         else begin
            item.data = data;
            data ++;        
         end
         driver_mailbox.put(item);
         @(driver_done_event);
      end     
   endtask
endclass // generator4


// The new driver class has a new configuration option that selects from
// the existing capability of driving tests each cycle, or alternatively
// producing one test at a time until the DUT completes, which is what we
// started with originally.

class driver5 #(int WIDTH, bit ONE_TEST_AT_A_TIME=1'b0);
   virtual           bit_diff_if #(.WIDTH(WIDTH)) vif;
   mailbox           driver_mailbox;
   mailbox           scoreboard_data_mailbox;
   event             driver_done_event;

   // New constructor to establish all connections.
   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) _vif, mailbox _driver_mailbox, 
                mailbox _scoreboard_data_mailbox, event _driver_done_event);
      vif = _vif;      
      driver_mailbox = _driver_mailbox;
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) item;
      $display("Time %0t [Driver]: Driver starting.", $time);

      // If doing one test at a time, go back to the original strategy of
      // waiting for DUT completion between tests.
      if (ONE_TEST_AT_A_TIME) begin
         forever begin
            driver_mailbox.get(item);
            vif.data = item.data;
            scoreboard_data_mailbox.put(item);
            vif.go = 1'b1;
            @(posedge vif.clk);
            vif.go = 1'b0;

            // Wait for DUT completion.
            @(posedge vif.clk iff (vif.done == 1'b0));   
            @(posedge vif.clk iff (vif.done == 1'b1));
            -> driver_done_event;           
         end
      end 
      else begin
         // To know whether or not generated inputs will create a DUT output, 
         // we need to know whether or not the DUT is currently active.
         logic is_first_test = 1'b1;      
         logic is_active = 1'b0;
         
         forever begin           
            // If the circuit is reset at any point, reset the driver state.
            while (vif.rst) begin
               @(posedge vif.clk);        
               is_first_test = 1'b1;
               is_active = 1'b0;                    
            end
            
            driver_mailbox.get(item);
            //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);
            
            vif.data = item.data;
            vif.go = item.go;
            @(posedge vif.clk);
            
            // If done is asserted, or if this is the first_test, 
            // then the DUT should be inactive and ready for another test.  
            if (vif.done || is_first_test)
              is_active = 1'b0;
            
            // If the DUT isn't already active, and we get a go signal, we are
            // starting a test, so inform the scoreboard. The scoreboard will
            // then wait to get the result from the monitor.     
            if (!is_active && vif.go) begin         
               $display("Time %0t [Driver]: Sending start of test for data=h%h.", $time, item.data);
               scoreboard_data_mailbox.put(item);
               is_active = 1'b1;            
               is_first_test = 1'b0;
            end
            
            -> driver_done_event;
         end
      end              
   endtask       
endclass


// The new evironment just connects all the new classes together, while
// taking the configuration options itself.

class env4 #(int NUM_TESTS, int WIDTH, 
             bit CONSECUTIVE_INPUTS=1'b0,
             bit ONE_TEST_AT_A_TIME=1'b0 );

   generator4 #(.WIDTH(WIDTH), .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS)) gen;
   driver5  #(.WIDTH(WIDTH), .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) drv;
   monitor3 #(.WIDTH(WIDTH)) monitor;
   scoreboard3 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) scoreboard;

   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) vif);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
      
      gen = new(driver_mailbox, driver_done_event);
      drv = new(vif, driver_mailbox, scoreboard_data_mailbox, driver_done_event);
      monitor = new(vif, scoreboard_result_mailbox);
      scoreboard = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new
     
   // Here we add a new report status method that can be called from outside
   // the environment (e.g., from the test class or main testbench).
   function void report_status();
      scoreboard.report_status();
   endfunction
   
   virtual task run();      
      fork
         gen.run();
         drv.run();
         monitor.run();
         scoreboard.run();       
      join_any

      disable fork;      
   endtask // run   
endclass // env4


// Here we see our first test class, which takes the same configuration options
// as the environment, in addition to a name for the test, and a number of
// repeats. For the specified repeats, the test will simply re-execute the
// environments run task as many times as specified.

class test #(string NAME="default_test_name", 
             int NUM_TESTS, 
             int WIDTH, 
             bit CONSECUTIVE_INPUTS=1'b0,
             bit ONE_TEST_AT_A_TIME=1'b0, 
             int REPEATS=0);

   virtual       bit_diff_if #(.WIDTH(WIDTH)) vif;
   env4 #(.NUM_TESTS(NUM_TESTS),
          .WIDTH(WIDTH),
          .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS),
          .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) e;

   // Test has its own constructor that initializes the interface.
   function new(virtual bit_diff_if #(.WIDTH(WIDTH)) _vif);
      vif = _vif;
      e = new(vif);      
   endfunction // new

   function void report_status();
      $display("Results for Test %0s", NAME);      
      e.report_status();
   endfunction
   
   task run();
      $display("Time %0t [Test]: Starting test %0s.", $time, NAME);

      // Repeat the tests the specified number of times.
      for (int i=0; i < REPEATS+1; i++) begin
         if (i > 0) $display("Time %0t [Test]: Repeating test %0s (pass %0d).", $time, NAME, i+1);       
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


// Module: bit_diff_tb7
// Description: This version of the testbench uses multiple test instances
// to illustrate how to configure and run multiple tests.

module bit_diff_tb7;

   localparam NUM_RANDOM_TESTS = 1000;
   localparam NUM_CONSECUTIVE_TESTS = 200;
   localparam NUM_REPEATS = 2;   
   localparam WIDTH = 16;   
   logic             clk;
      
   bit_diff_if #(.WIDTH(WIDTH)) _if (.clk(clk));   
   bit_diff DUT (.clk(clk), .rst(_if.rst), .go(_if.go), 
            .done(_if.done), .data(_if.data), .result(_if.result));

   // Create one test for the normal random testing.
   test #(.NAME("Random Test"), .NUM_TESTS(NUM_RANDOM_TESTS), .WIDTH(WIDTH), .REPEATS(NUM_REPEATS)) test0 = new(_if);

   // Create one test for the normal random testing.
   test #(.NAME("Consecutive Test"), .NUM_TESTS(NUM_CONSECUTIVE_TESTS), .WIDTH(WIDTH), .CONSECUTIVE_INPUTS(1'b1), .ONE_TEST_AT_A_TIME(1'b1), .REPEATS(NUM_REPEATS)) test1 = new(_if);
   
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


// The current testbench provides a decent set of functionality, but still has
// some significant limitations.
// -In multiple places, we are reusing code that waits for the DUT to finish. 
//  Whenever possible, code should not be repeated because it will inevitably 
//  lead to errors at some point when one copy is changed but another is not.
// -The driver has too many responsibilities. It both has to drive inputs and
//  detect when one of those inputs starts the DUT so it can inform the
//  scoreboard. In general, we should try to simplify each class so that it
//  has one specific responsibility. This greatly improves scalability of code
//  because when the handling of one responsibility is changed, it won't affect
//  other parts of the code.
// -Detecting the start of a test requires a lot of low level knowledge about
//  when the DUT is active or inactive. Ideally, the testbench code wouldn't
//  need to be exposed to this level of detail.

// We fix most of these problems with a new interface that provides multiple
// abstract methods that hide low-level implementation details. Such an
// abstraction is often referred to as a bus functional model (BFM).

interface bit_diff_bfm #(parameter int WIDTH) (input logic clk);
   logic             rst, go, done;
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   // With this wait_for_done task, the method for waiting to completion is 
   // defined in one place, which makes it easy to change. The implementation 
   // details are also hidden from the rest of the testbench, which makes it
   // more readable and concise.
   //
   // IMPORTANT: If there is any chance of these tasks being called by multiple
   // threads during the same timestep, they need to be automatic.
   // Remove the automatic keyword to see what happens. In my tests, only
   // one thread would match these events, requiring all other threads to wait
   // until they happen again, which means a monitor could miss seeing done
   // if it was only asserted for one cycle.
   task automatic wait_for_done();
      @(posedge clk iff (done == 1'b0));
      @(posedge clk iff (done == 1'b1));      
   endtask
 
   // Similarly, we can create other commonly used functionality that can be
   // called from different points in our testbench. These tasks are very useful
   // because they provide a layer of abstraction where common functionality
   // has a single definition within the BFM.
   
   // Reset the design.
   task automatic reset(int cycles);
      rst = 1'b1;
      go = 1'b0;      
      for (int i=0; i < cycles; i++) @(posedge clk);
      rst = 1'b0;
      @(posedge clk);      
   endtask

   // Start the DUT with the specified data by creating a 1-cycle pulse on go.
   task automatic start(input logic [WIDTH-1:0] data_);    
      data = data_;
      go = 1'b1;      
      @(posedge clk);

      // IMPORTANT: This has to be a non-blocking assignment to give other 
      // threads a chance to see that go was 1 on this rising edge. 
      // Alternatively, you could wait for a small amount of time before setting
      // it back to 0.
      go <= 1'b0;    
   endtask // start
   
   // Helper code to detect when the DUT starts executing. This task internally
   // tracks the active status of the DUT and sends an event every time it
   // becomes active. With this strategy, the implementation specific details
   // are limited to the BFM and are hidden from the testbench.
   event active_event;      
   task automatic monitor();
      logic is_active;
      is_active = 1'b0;
            
      forever begin
         @(posedge clk);
         if (rst) is_active = 1'b0;
         else begin         
            if (done) is_active = 1'b0;     
            if (!is_active && go) begin                
               is_active = 1'b1;
               // The event is needed because there will be times in the
               // simulation where go and done are asserted at the same time.
               // If the code simply used @(posedge is_active) to detect the
               // start of a test, it would miss these instances because 
               // there wouldn't be a rising edge on is_active. It would simply
               // remain active between two consecutive tests.
               -> active_event;        
            end
         end
      end      
   endtask // monitor
endinterface


// The new driver class uses the new BFM, and also no longer monitors for the
// beginning of tests, which eliminates the need for the scoreboard mailbox.

class driver6 #(int WIDTH, bit ONE_TEST_AT_A_TIME=1'b0);
   virtual           bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   mailbox           driver_mailbox;
   event             driver_done_event;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm, 
                mailbox _driver_mailbox, 
                event   _driver_done_event);
      this.bfm = bfm;      
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      bit_diff_item3 #(.WIDTH(WIDTH)) item;
      $display("Time %0t [Driver]: Driver starting.", $time);

      if (ONE_TEST_AT_A_TIME) begin
         forever begin
            driver_mailbox.get(item);

            // With the new BFM, we can just call the start method instead of
            // driving the signals directly.
            bfm.start(item.data);

            // Similarly, now we call the BFM to Wait for DUT completion, which
            // makes the driver independent of the implementation details.
            bfm.wait_for_done();            
            $display("Time %0t [Driver]: Detected done.", $time);           
            -> driver_done_event;           
         end
      end 
      else begin         
         forever begin                      
            driver_mailbox.get(item);
            //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);

            // Here we don't use the BFM start method simply because we don't
            // necessarily want to start the DUT. We just want to drive the
            // inputs
            bfm.data = item.data;
            bfm.go = item.go;
            @(posedge bfm.clk);
            -> driver_done_event;
         end
      end              
   endtask       
endclass


// The done_monitor class is the previous, but since there are now multiple
// monitoring responsibilities, this class is solely responsible for monitoring
// for done events.

class done_monitor #(int WIDTH);
   virtual           bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   mailbox           scoreboard_result_mailbox;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm, 
                mailbox _scoreboard_result_mailbox);
      this.bfm = bfm;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
   
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item = new;

         // Here we use the BFM method to make the monitor independent from the
         // wait implementation.
         bfm.wait_for_done();
         item.result = bfm.result;
         $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, bfm.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


// Here we create a new class start_monitor that replaces the responsibility
// of detecting when the DUT is started, which was previously handled by the
// driver.

class start_monitor #(int WIDTH);
   virtual           bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   mailbox           scoreboard_data_mailbox;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm, 
                mailbox _scoreboard_data_mailbox);
      this.bfm = bfm;      
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
   endfunction // new

   task run();
      fork
         // Start the BFM monitor to track the active status.
         bfm.monitor();
         detect_start();         
      join_any
   endtask
   
   task detect_start();    
      forever begin
         bit_diff_item3 #(.WIDTH(WIDTH)) item = new;

         // Wait until the DUT becomes active.
         @(bfm.active_event);    
         item.data = bfm.data;   
         $display("Time %0t [start_monitor]: Sending start of test for data=h%h.", $time, item.data);
         scoreboard_data_mailbox.put(item);      
      end              
   endtask       
endclass


// This new environment simply updates the driver and monitors.

class env5 #(int NUM_TESTS, int WIDTH, 
             bit CONSECUTIVE_INPUTS=1'b0,
             bit ONE_TEST_AT_A_TIME=1'b0 );

   // I tend to use an _h suffix for handles to avoid variables having the same
   // name as the class. Since I use done_monitor_h and start_monitor_h, I
   // made all the other use the same convention.
   //
   // I have no idea why the conventional style of SystemVerilog is to not
   // capitalize class names like in other OOP languages. For example,
   //    Done_monitor #(.WIDTH(WIDTH)) done_monitor
   // would solve this problem. I have also seen other people simply add a
   // number suffix, or sometimes a _ suffix or prefix.
   generator4 #(.WIDTH(WIDTH), .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS)) gen_h;
   driver6  #(.WIDTH(WIDTH), .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) drv_h;
   done_monitor #(.WIDTH(WIDTH)) done_monitor_h;
   start_monitor #(.WIDTH(WIDTH)) start_monitor_h;
   scoreboard3 #(.NUM_TESTS(NUM_TESTS), .WIDTH(WIDTH)) scoreboard_h;

   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
      
      gen_h = new(driver_mailbox, driver_done_event);
      drv_h = new(bfm, driver_mailbox, driver_done_event);
      done_monitor_h = new(bfm, scoreboard_result_mailbox);
      start_monitor_h = new(bfm, scoreboard_data_mailbox);
      scoreboard_h = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new
     
   // Here we add a new report status method that can be called from outside
   // the environment (e.g., from the test class or main testbench).
   function void report_status();
      scoreboard_h.report_status();
   endfunction
   
   virtual task run();      
      fork
         gen_h.run();
         drv_h.run();
         done_monitor_h.run();
         start_monitor_h.run();
         scoreboard_h.run();     
      join_any

      disable fork;      
   endtask // run   
endclass // env5


// The new test class uses the new environment, and replaces some code with a
// call to a BFM method.

class test2 #(string NAME="default_test_name", 
              int NUM_TESTS, 
              int WIDTH, 
              bit CONSECUTIVE_INPUTS=1'b0,
              bit ONE_TEST_AT_A_TIME=1'b0, 
              int REPEATS=0);

   virtual        bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   env5 #(.NUM_TESTS(NUM_TESTS),
          .WIDTH(WIDTH),
          .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS),
          .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) env_h;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);
      this.bfm = bfm;
      env_h = new(bfm);
   endfunction // new

   function void report_status();
      $display("Results for Test %0s", NAME);      
      env_h.report_status();
   endfunction
   
   task run();
      $display("Time %0t [Test]: Starting test %0s.", $time, NAME);
      
      // Repeat the tests the specified number of times.
      for (int i=0; i < REPEATS+1; i++) begin
         if (i > 0) $display("Time %0t [Test]: Repeating test %0s (pass %0d).", $time, NAME, i+1);
         
         // We update the test to use the BFM reset method.
         bfm.reset(5);
         env_h.run();
         @(posedge bfm.clk);     
      end
      $display("Time %0t [Test]: Test completed.", $time);      
   endtask   
endclass


// Module: bit_diff_tb8
// Description: This testbench uses the new BFM and test2 class.

module bit_diff_tb8;

   localparam NUM_RANDOM_TESTS = 1000;
   localparam NUM_CONSECUTIVE_TESTS = 200;
   localparam NUM_REPEATS = 4;   
   localparam WIDTH = 16;   
   logic             clk;
   
   bit_diff_bfm #(.WIDTH(WIDTH)) bfm (.clk(clk));   
   bit_diff DUT (.clk(clk), .rst(bfm.rst), .go(bfm.go), 
            .done(bfm.done), .data(bfm.data), .result(bfm.result));

   test2 #(.NAME("Random Test"), .NUM_TESTS(NUM_RANDOM_TESTS), .WIDTH(WIDTH), .REPEATS(NUM_REPEATS)) test0 = new(bfm);
   test2 #(.NAME("Consecutive Test"), .NUM_TESTS(NUM_CONSECUTIVE_TESTS), .WIDTH(WIDTH), .CONSECUTIVE_INPUTS(1'b1), .ONE_TEST_AT_A_TIME(1'b1), .REPEATS(NUM_REPEATS)) test1 = new(bfm);
   
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
      
   assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.go && bfm.done |=> !bfm.done);
     
endmodule // bit_diff_tb8



// If you made it this far, wow, I'm impressed.
