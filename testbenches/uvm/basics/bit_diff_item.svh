// Greg Stitt
// University of Florida

// In UVM, the transaction is generally defined by a "sequence item." The
// sequence item contains all the fields that are needed to communicate with
// the DUT, at whatever level of abstraction you choose. An abstract sequence
// item will look nothing like the DUT's interface, whereas a low-level sequence
// item might look nearly identical to the DUT's interface.

`ifndef _BIT_DIFF_ITEM_SVH_
`define _BIT_DIFF_ITEM_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import bit_diff_if_pkg::*;

class bit_diff_item extends uvm_sequence_item;
    // Get the width from the testbench package. This avoids having to parameterize
    // this class, which would in turn require parameters every place where this
    // class is used.
    localparam int WIDTH = bit_diff_if_pkg::WIDTH;

    // For now, our sequence item solely contains the data input for which the
    // DUT will compute the bit_diff. All other DUT I/O are omitted, with the
    // go input being generated automaticall by the driver.
    rand bit [WIDTH-1:0] data;

    // This macro is used to declare that the class bit_diff_item is a UVM 
    // object. It sets up the necessary UVM internals to support object
    // management, such as object creation, printing, and comparison. It also
    // registers the class with the factory.
    `uvm_object_utils_begin(bit_diff_item)

    // This macro is used to register a member variable, data, as a field in
    // the bit_diff_item class.  In this case, UVM_ALL_ON means that all 
    // features related to this field are enabled (e.g., printing, comparing, 
    // and copying of the field).
        `uvm_field_int(data, UVM_ALL_ON)        
    `uvm_object_utils_end

    function new(string name = "bit_diff_item");
        super.new(name);
    endfunction

endclass

`endif
