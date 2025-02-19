// Greg Stitt
// University of Florida

`ifndef _ACCUM_SEQUENCE_SVH_
`define _ACCUM_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

import accum_tb_pkg::*;


virtual class accum_base_sequence extends uvm_sequence #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH));
    `uvm_object_utils(accum_base_sequence)

    int num_tests;
    bit is_packet_level;

    function new(string name = "accum_sequence");
        super.new(name);
        if (!uvm_config_db#(int)::get(this, "", "num_tests", num_tests)) `uvm_fatal("NO_NUM_TESTS", "num_tests not specified.");
    endfunction
endclass


class accum_beat_sequence extends accum_base_sequence;
    `uvm_object_utils(accum_beat_sequence)

    function new(string name = "accum_beat_sequence");
        super.new(name);
        is_packet_level = 1'b0;
    endfunction

    virtual task body();
        for (int i = 0; i < num_tests; i++) begin
            req = axi4_stream_seq_item#(accum_tb_pkg::INPUT_WIDTH)::type_id::create($sformatf("req%0d", i));
            wait_for_grant();

            void'(req.randomize() with {
                tdata.size() == 1;
                tstrb.size() == 1;
                tkeep.size() == 1;
                tdata[0] dist {
                    '0                                       :/ 2,
                    '1                                       :/ 2,
                    [0 : 2 ** accum_tb_pkg::INPUT_WIDTH - 2] :/ 96
                };
                tlast dist {
                    1 :/ 70,
                    0 :/ 30
                };
                tstrb[0] == '1;
                tkeep[0] == '1;
            });

            send_request(req);
            wait_for_item_done();
        end
    endtask
endclass


class accum_packet_sequence extends accum_base_sequence;
    `uvm_object_utils(accum_packet_sequence)

    function new(string name = "accum_packet_sequence");
        super.new(name);
        is_packet_level = 1'b0;
    endfunction

    virtual task body();
        for (int i = 0; i < num_tests; i++) begin
            req = axi4_stream_seq_item#(accum_tb_pkg::INPUT_WIDTH)::type_id::create($sformatf("req%0d", i));
            wait_for_grant();

            assert(req.randomize() with {
                tdata.size() == 10;
                tstrb.size() == 10;
                tkeep.size() == 10;
                foreach (tdata[i]) {
                    tdata[i] dist {
                        '0                                       :/ 2,
                        '1                                       :/ 2,
                        [0 : 2 ** accum_tb_pkg::INPUT_WIDTH - 2] :/ 96
                    };
                    tstrb[i] == '1;
                    tkeep[i] == '1;
                }
            }) else $fatal(1, "Randomization failed.");

            req.tlast = 1'bX;

            send_request(req);
            wait_for_item_done();
        end
    endtask
endclass


`endif
