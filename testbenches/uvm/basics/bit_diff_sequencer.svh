// Greg Stitt
// University of Florida

// A UVM sequencer is responsible for managing the flow of sequence items from 
// potentially multiple sequences into a driver. It provides mechanisms to 
// control and manage the execution of these sequences.
//
// Sequencers can become quite complex when dealing with intricate interfaces 
// that require specific timings for sequence items, which may be of different 
// types.
    
// Fortunately, in many cases, when you’re feeding a single type of sequence to
// a driver, the uvm_sequencer class already provides all the necessary 
// functionality. This is why, in this example, the sequencer extends the 
// uvm_sequencer class without adding any additional functionality.

`ifndef _BIT_DIFF_SEQUENCER_SVH_
`define _BIT_DIFF_SEQUENCER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"

class bit_diff_sequencer extends uvm_sequencer #(bit_diff_item);
    `uvm_component_utils(bit_diff_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass


`endif
