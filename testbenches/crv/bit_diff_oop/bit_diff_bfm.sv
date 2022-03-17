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
      rst <= 1'b1;
      go <= 1'b0;      
      for (int i=0; i < cycles; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
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
