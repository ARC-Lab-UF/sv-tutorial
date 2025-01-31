`ifndef _BIT_DIFF_DRIVER_SVH_
`define _BIT_DIFF_DRIVER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"

class bit_diff_driver extends uvm_driver #(bit_diff_item);
    `uvm_component_utils(bit_diff_driver)

    virtual bit_diff_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual bit_diff_if)::get(this, "", "vif", vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
    endfunction

    virtual task run_phase(uvm_phase phase);

        // Use the interfaces's built-in reset. We could have also directly
        // driven the reset signal here, but using interface methods is a 
        // good idea in case you have multiple drivers, which prevents 
        // replicated code.    
        vif.reset(5);

        // The driver runs for ever, waiting for sequence items from a sequence/
        // sequencer. Upon receiving a sequence item, it then drives that
        // transaction onto the DUT interface, and then notices the sequencer
        // that it is done with the transaction.
        forever begin
            // Request a new sequence item from the sequencer.
            seq_item_port.get_next_item(req);

            // Drive the DUT by converting transaction signals to DUT interface
            // signals. In this example, the transaction and interface signals
            // happen to be the same, but when using standard interfaces (e.g., 
            // AXI), the structure of the transaction and interface can be quite
            // different. This code performs the translation, allowing the rest 
            // of the testbench to focus on transactions at an appropriate level
            // of abstraction, rather than dealing with the specifics of the 
            // interface.
            //
            // In most cases, from what I've seen, it would be more common to
            // treat just the data as the transaction, with the driver implicitly
            // assertion go for every sequence item. However, while good for
            // feature testing, that strategy wouldn't test go being asserted
            // during the execution of the DUT, which is a likely candidate for
            // causing errors. This is an example of why it might make sense
            // to have different sequence items and different drivers to ensure
            // that you achieve better coverage.
            vif.data <= req.data;
            vif.go <= req.go;
            @(posedge vif.clk);

            // Notify the sequencer that the current sequence item has been 
            // completed, allowing the sequencer to proceed with the next item 
            // in the sequence or handle other tasks.
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
