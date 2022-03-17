// Gerg Stitt
// University of Florida

`ifndef _ENVIRONMENT_SVH_
`define _ENVIRONMENT_SVH_

`include "driver.svh"
`include "generator.svh"
`include "monitor.svh"
`include "scoreboard.svh"

class environment #(int WIDTH);

   // The environment doesn't know what type of generator and driver it will
   // use, so it contains a handle to the base class for each. Use of virtual
   // methods then allows us to use any class derived from the base version
   // without requiring knowledge of the specific class here.
   base_generator #(.WIDTH(WIDTH)) genarator_h;
   base_driver  #(.WIDTH(WIDTH)) driver_h;
   done_monitor #(.WIDTH(WIDTH)) done_monitor_h;
   start_monitor #(.WIDTH(WIDTH)) start_monitor_h;
   scoreboard #(.WIDTH(WIDTH)) scoreboard_h;

   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm,
                base_generator #(.WIDTH(WIDTH)) gen_h, 
                base_driver #(.WIDTH(WIDTH)) drv_h);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;

      // We no longer instantiate these here because they are created in the
      // test class and passed in to this constructor.
      genarator_h = gen_h;     
      driver_h = drv_h;      
      done_monitor_h = new(bfm, scoreboard_result_mailbox);
      start_monitor_h = new(bfm, scoreboard_data_mailbox);
      scoreboard_h = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new
     
   function void report_status();
      scoreboard_h.report_status();
   endfunction
   
   virtual task run(int num_tests);   
      fork
         genarator_h.run();
         driver_h.run();
         done_monitor_h.run();
         start_monitor_h.run();
         scoreboard_h.run(num_tests);    
      join_any

      disable fork;      
   endtask 
endclass

`endif
