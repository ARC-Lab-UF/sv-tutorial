// Greg Stitt
// University of Florida

// This class defines a sequence to test each multiplier input. It simply
// creates random axi4_stream_seq_items.

`ifndef _MULT_SEQUENCE_SVH_
`define _MULT_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

import mult_tb_pkg::*;

// This syntax can be confusing. Mult_sequence is derived from uvm_sequence, but
// uvm_sequence is parameterized based on the seq item. So, we have to specify 
// the axi4_stream_seq_item. But, that sequenece item is also parameterized based
// on the input width specified in mult_tb_pkg. This confusing parameterization
// is one reason people avoid this strategy for parameterized interfaces.
// However, it is important to understand before trying other methods.
class mult_sequence extends uvm_sequence #(axi4_stream_seq_item #(mult_tb_pkg::INPUT_WIDTH));
    `uvm_object_utils(mult_sequence)

    int num_tests;

    function new(string name = "mult_sequence");
        super.new(name);
        if (!uvm_config_db#(int)::get(this, "", "num_tests", num_tests)) `uvm_fatal("NO_NUM_TESTS", "num_tests not specified.");
    endfunction

    virtual task body();
        for (int i = 0; i < num_tests; i++) begin
            req = axi4_stream_seq_item#(mult_tb_pkg::INPUT_WIDTH)::type_id::create($sformatf("req%0d", i));
            wait_for_grant();
            void'(req.randomize());
            send_request(req);
            wait_for_item_done();
        end
    endtask
endclass


`endif
