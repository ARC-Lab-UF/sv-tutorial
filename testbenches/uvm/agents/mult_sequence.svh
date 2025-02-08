`ifndef _MULT_SEQUENCE_SVH_
`define _MULT_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"
`include "axi4_stream_sequencer.svh"

import mult_tb_pkg::*;

class mult_sequence extends uvm_sequence #(axi4_stream_seq_item);
    `uvm_object_utils(mult_sequence)

    int num_tests;

    function new(string name = "mult_sequence");
        super.new(name);
        if (!uvm_config_db#(int)::get(this, "", "num_tests", num_tests)) `uvm_fatal("NO_NUM_TESTS", "num_tests not specified.");
    endfunction

    virtual task body();
        axi4_stream_seq_item#(mult_tb_pkg::INPUT_WIDTH) req;

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
