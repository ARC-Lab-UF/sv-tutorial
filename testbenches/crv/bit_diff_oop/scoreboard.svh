// Greg Stitt
// University of Florida

`ifndef _SCOREBOARD_SVH_
`define _SCOREBOARD_SVH_

`include "bit_diff_item.svh"

class scoreboard #(int WIDTH);
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_data_mailbox;
   int     passed, failed, reference;

   function new(mailbox scoreboard_data_mailbox, mailbox scoreboard_result_mailbox);
      this.scoreboard_data_mailbox = scoreboard_data_mailbox;
      this.scoreboard_result_mailbox = scoreboard_result_mailbox;
      
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

   task run(int num_tests);
      bit_diff_item #(.WIDTH(WIDTH)) in_item;   
      bit_diff_item #(.WIDTH(WIDTH)) out_item;   
            
      for (int i=0; i < num_tests; i++) begin
                
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
      end // for (int i=0; i < num_tests; i++)

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
   
endclass

`endif
