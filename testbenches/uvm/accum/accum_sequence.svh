// Greg Stitt
// University of Florida

// This file defines both single-beat and packet-level sequences.

`ifndef _ACCUM_SEQUENCE_SVH_
`define _ACCUM_SEQUENCE_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "axi4_stream_seq_item.svh"

import accum_tb_pkg::*;

// Create a base sequence that provides common functionality.
virtual class accum_base_sequence extends uvm_sequence #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH));
    `uvm_object_utils(accum_base_sequence)

    int num_packets;
    bit is_packet_level;

    int min_packet_size;
    int max_packet_size;

    function new(string name = "accum_sequence");
        super.new(name);
        if (!uvm_config_db#(int)::get(this, "", "num_packets", num_packets)) `uvm_fatal("NO_NUM_PACKETS", "num_packets not specified.");
        if (!uvm_config_db#(int)::get(this, "", "min_packet_size", min_packet_size)) `uvm_fatal("NO_MIN_PACKET_SIZE", "min_packet_size not specified.");
        if (!uvm_config_db#(int)::get(this, "", "max_packet_size", max_packet_size)) `uvm_fatal("NO_MAX_PACKET_SIZE", "max_packet_size not specified.");
    endfunction
endclass


// Sequence of individual axi_stream_seq_item beats.
class accum_beat_sequence extends accum_base_sequence;
    `uvm_object_utils(accum_beat_sequence)

    function new(string name = "accum_beat_sequence");
        super.new(name);
        is_packet_level = 1'b0;
    endfunction

    virtual task body();
        int packet_size;
        int count = 0;

        for (int i = 0; i < num_packets; i++) begin

            // Randomly select a packet size.
            packet_size = $urandom_range(min_packet_size, max_packet_size);

            // Create all items in the packet.
            for (int j = 0; j < packet_size; j++) begin

                req = axi4_stream_seq_item#(accum_tb_pkg::INPUT_WIDTH)::type_id::create($sformatf("req%0d", count++));
                wait_for_grant();

                // Randomize individual beats.
                assert(req.randomize() with {
                    tdata.size() == 1;
                    tdata[0] dist {
                        '0                                       :/ 2,
                        '1                                       :/ 2,
                        [0 : 2 ** accum_tb_pkg::INPUT_WIDTH - 2] :/ 96
                    };
                    (j == packet_size-1) -> tlast == 1'b1;
                    (j < packet_size-1) -> tlast == 1'b0;              
                    tstrb[0] == '1;
                    tkeep[0] == '1;
                    is_packet_level == 1'b0;
                }) else $fatal(1, "Randomization failed.");

                // Send the individual beat before completing the entire packet.
                send_request(req);
                wait_for_item_done();
            end
        end
    endtask
endclass

// Sequence of packetes of axi_stream_seq_items.
class accum_packet_sequence extends accum_base_sequence;
    `uvm_object_utils(accum_packet_sequence)

    function new(string name = "accum_packet_sequence");
        super.new(name);
        is_packet_level = 1'b1;
    endfunction

    virtual task body();
        for (int i = 0; i < num_packets; i++) begin
            req = axi4_stream_seq_item#(accum_tb_pkg::INPUT_WIDTH)::type_id::create($sformatf("req%0d", i));
            wait_for_grant();

            req.is_packet_level = 1'b1;

            // Randomize the entire packet.
            assert (req.randomize() with {
                tdata.size() inside {[min_packet_size : max_packet_size]};
                foreach (tdata[i]) {
                    tdata[i] dist {
                        '0                                       :/ 2,
                        '1                                       :/ 2000,
                        [0 : 2 ** accum_tb_pkg::INPUT_WIDTH - 2] :/ 96
                    };                
                    tstrb[i] == '1;
                    tkeep[i] == '1;
                }
                is_packet_level == 1'b1;
            })
            else $fatal(1, "Randomization failed.");

            // tlast is undefined for a packet-level transaction. The driver
            // will set tlast automatically when reaching the final beat.
            req.tlast = 1'bX;

            // Send the entire packet.
            send_request(req);
            wait_for_item_done();
        end
    endtask
endclass


`endif
