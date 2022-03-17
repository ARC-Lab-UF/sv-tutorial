// Greg Stitt
// University of Florida

`ifndef _DRIVER_SVH_
`define _DRIVER_SVH_

`include "bit_diff_item.svh"

virtual class base_driver #(int WIDTH);
   virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm;
   mailbox driver_mailbox;
   event   driver_done_event;
   
   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);
      this.bfm = bfm;     
      driver_mailbox = new;
   endfunction // new

   pure virtual task run();
endclass // base_driver


class nonblocking_driver #(int WIDTH) extends base_driver #(.WIDTH(WIDTH));

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);
      super.new(bfm);      
   endfunction // new
   
   virtual task run();
      bit_diff_item #(.WIDTH(WIDTH)) item;
      $display("Time %0t [Driver]: Driver starting.", $time);
      
      forever begin                         
         driver_mailbox.get(item);
         //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);  
         bfm.data = item.data;
         bfm.go = item.go;
         @(posedge bfm.clk);
         -> driver_done_event;
      end      
   endtask          
endclass

   
class blocking_driver #(int WIDTH) extends base_driver #(.WIDTH(WIDTH));  

   function new(virtual bit_diff_bfm #(.WIDTH(WIDTH)) bfm);
      super.new(bfm);      
   endfunction // new
   
   task run();
      bit_diff_item #(.WIDTH(WIDTH)) item;
      $display("Time %0t [Driver]: Driver starting.", $time);

      forever begin
         driver_mailbox.get(item);
         bfm.start(item.data);   
         bfm.wait_for_done();       
         $display("Time %0t [Driver]: Detected done.", $time);      
         -> driver_done_event;      
      end
   endtask       
endclass 

`endif
