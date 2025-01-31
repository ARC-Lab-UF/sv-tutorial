`ifndef _BIT_DIFF_ITEM_SVH_
`define _BIT_DIFF_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

class bit_diff_item extends uvm_sequence_item;

    parameter int WIDTH = 8;
    rand bit [WIDTH-1:0] data;
    rand bit go;
    bit signed [$clog2(WIDTH*2-1)-1:0] result;

    `uvm_object_utils_begin(bit_diff_item)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(go, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "bit_diff_item");
        super.new(name);
    endfunction

    constraint c_go_dist {
        go dist {
            0 :/ 90,
            1 :/ 10
        };
    }

endclass

`endif
