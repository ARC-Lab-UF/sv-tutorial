// Greg Stitt
// University of Florida

interface bit_diff_bfm #(parameter int WIDTH) (input logic clk);
   logic             rst, go, done;
   logic [WIDTH-1:0] data;
   logic signed [$clog2(2*WIDTH+1)-1:0] result;

   task automatic wait_for_done();
      @(posedge clk iff (done == 1'b0));
      @(posedge clk iff (done == 1'b1));      
   endtask
 
   task automatic reset(int cycles);
      rst <= 1'b1;
      go <= 1'b0;      
      for (int i=0; i < cycles; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);      
   endtask

   task automatic start(input logic [WIDTH-1:0] data_);    
      data <= data_;
      go <= 1'b1;      
      @(posedge clk);
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
