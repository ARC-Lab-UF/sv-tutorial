// Greg Stitt
// University of Florida

`ifndef _MONITOR_SVH_
`define _MONITOR_SVH_

`include "bit_diff_item.svh"

virtual class base_monitor #(int WIDTH);
   virtual           bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   
   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);
      this.bfm = bfm;
   endfunction // new

   pure virtual task run();
endclass
   

class done_monitor #(int WIDTH) extends base_monitor #(.WIDTH(WIDTH));
   mailbox           scoreboard_result_mailbox;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm, 
                mailbox _scoreboard_result_mailbox);
      super.new(bfm);
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
   
   virtual task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         bit_diff_item #(.WIDTH(WIDTH)) item = new;
         bfm.wait_for_done();
         item.result = bfm.result;
         $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, bfm.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass


class start_monitor #(int WIDTH) extends base_monitor #(.WIDTH(WIDTH));
   mailbox           scoreboard_data_mailbox;

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm, 
                mailbox _scoreboard_data_mailbox);
      super.new(bfm);      
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
   endfunction // new

   virtual task run();
      fork
         // Start the BFM monitor to track the active status.
         bfm.monitor();
         detect_start();         
      join_any
   endtask
   
   task detect_start();     
      forever begin
         bit_diff_item #(.WIDTH(WIDTH)) item = new;

         // Wait until the DUT becomes active.
         @(bfm.active_event);    
         item.data = bfm.data;   
         $display("Time %0t [start_monitor]: Sending start of test for data=h%h.", $time, item.data);
         scoreboard_data_mailbox.put(item);      
      end              
   endtask       
endclass

`endif
