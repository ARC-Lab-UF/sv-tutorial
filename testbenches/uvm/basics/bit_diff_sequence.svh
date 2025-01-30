`ifndef _BIT_DIFF_SEQUENCE_SVH_
`define _BIT_DIFF_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"
`include "bit_diff_sequencer.svh"

class bit_diff_sequence extends uvm_sequence#(bit_diff_item);
    `uvm_object_utils(bit_diff_sequence)

    int num_tests;

    function new(string name="bit_diff_sequence");        
        super.new(name);

        if (!uvm_config_db#(int)::get(this, "", "num_tests", num_tests)) `uvm_fatal("NO_NUM_TESTS", "num_tests not specified.");        
    endfunction

    virtual task body();        
        for (int i=0; i < num_tests; i++) begin
            // Create a sequence item (i.e., transaction) to send to the driver.
            req = bit_diff_item::type_id::create($sformatf("req%0d", i));

            // Wait for the sequencer to give permission to send a request.
            wait_for_grant();

            // Randomize our transaction. This is normally where most of the
            // sequence logic goes, but in our case, we just want a sequence
            // of randomized transacations, based on the constraints specified
            // in bit_diff_item.
            req.randomize();

            // Send the request to the sequencer to send to the driver.
            send_request(req);

            // Wait for the sequencer to tell us that the sequencer item
            // has completed.
            wait_for_item_done();
        end
    endtask
endclass


`endif
