// Greg Stitt
// University of Florida

`ifndef _BIT_DIFF_DRIVER_SVH_
`define _BIT_DIFF_DRIVER_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"

class bit_diff_driver extends uvm_driver #(bit_diff_item);
    `uvm_component_utils(bit_diff_driver)

    // The driver also needs the virtual interface, which it obtains via the
    // uvm_config_db.
    virtual bit_diff_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual bit_diff_if)::get(this, "", "vif", vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
    endfunction

    virtual task run_phase(uvm_phase phase);

        // Wait until the design has been reset before driving any transactions.
        @(posedge vif.clk iff vif.rst);
        @(posedge vif.clk iff !vif.rst);

        // The driver runs for ever, waiting for sequence items from a sequence/
        // sequencer. Upon receiving a sequence item, it then drives that
        // transaction onto the DUT interface, and then notices the sequencer
        // that it is done with the transaction.
        forever begin
            // Request a new sequence item from the sequencer.
            seq_item_port.get_next_item(req);

            // Drive the DUT by converting transaction signals to DUT interface
            // signals. For our simple transaction, the sequence item provides
            // the data input for which the DUT should compute the bit_diff.
            // The only missing information is the go signal, which the DUT
            // drives automatically when receiving the data.            
            vif.data <= req.data;
            vif.go <= 1'b1;
            @(posedge vif.clk);
            vif.go <= 1'b0;
            @(posedge vif.clk);

            // We need to wait for done before driving the next transaction
            // otherwise the DUT will ignore it.
            vif.wait_for_done();

            // Wait some amount of time between tests. Not necessary, just for
            // demonstration. In many cases, it might be good to randomize this
            // amount, or to have it provided by the sequence item itself.
            repeat(5) @(posedge vif.clk);

            // Notify the sequencer that the current sequence item has been 
            // completed, allowing the sequencer to proceed with the next item 
            // in the sequence or handle other tasks.
            seq_item_port.item_done();
        end
    endtask
endclass


`endif
