// Greg Stitt
// University of Florida

`ifndef _GENERATOR_SVH_
`define _GENERATOR_SVH_

`include "driver.svh"

virtual class base_generator #(int WIDTH);
  
   mailbox driver_mailbox;
   event   driver_done_event;
   
   function new(base_driver #(.WIDTH(WIDTH)) driver_h);      
      this.driver_mailbox = driver_h.driver_mailbox;
      this.driver_done_event = driver_h.driver_done_event;      
   endfunction // new

   pure virtual task run();      
endclass


class random_generator #(int WIDTH) extends base_generator #(.WIDTH(WIDTH));

   function new(base_driver #(.WIDTH(WIDTH)) driver_h);      
      super.new(driver_h);      
   endfunction // new
   
   virtual task run();
      bit_diff_item #(.WIDTH(WIDTH)) item;

      // Start the consecutive sequence at 0. This could also be modified with
      // another configuration parameter.
      bit [WIDTH-1:0] data = '0;     
      
      forever begin
         item = new;             
         if (!item.randomize()) $display("Randomize failed");    
         driver_mailbox.put(item);
         @(driver_done_event);
      end     
   endtask
endclass 

 
class consecutive_generator #(int WIDTH) extends base_generator #(.WIDTH(WIDTH));

   function new(base_driver #(.WIDTH(WIDTH)) driver_h);      
      super.new(driver_h);      
   endfunction // new
  
   task run();
      bit_diff_item #(.WIDTH(WIDTH)) item;
      bit [WIDTH-1:0] data = '0;     
      
      forever begin
         item = new;     
         item.data = data;
         data ++;
         driver_mailbox.put(item);
         @(driver_done_event);
      end     
   endtask
endclass

`endif
