`ifndef _MULT_SEQUENCE_SVH_
`define _MULT_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"
`include "axi4_stream_sequencer.svh"

class mult_sequence #(
    parameter int DATA_WIDTH = 32
) extends uvm_sequence #(axi4_stream_seq_item);
    `uvm_component_param_utils(mult_sequence#(DATA_WIDTH))

    int num_tests;

    function new(string name = "mult_sequence");
        super.new(name);
        if (!uvm_config_db#(int)::get(this, "", "num_tests", num_tests)) `uvm_fatal("NO_NUM_TESTS", "num_tests not specified.");
    endfunction

    virtual task body();
        for (int i = 0; i < num_tests; i++) begin
            req = axi4_stream_seq_item#(DATA_WIDTH)::type_id::create($sformatf("req%0d", i));
            wait_for_grant();
            req.randomize();
            send_request(req);
            wait_for_item_done();
        end
    endtask
endclass


`endif
