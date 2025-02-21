// Greg Stitt
// Wes Piard
// University of Florida

// A simplified subset of the AXI4 streaming interface. I've included all the 
// signal in the normal interface, but commented out the optional ones we won't
// be supporting in this example.

`ifndef _AXI4_STREAM_IF_
`define _AXI4_STREAM_IF_

interface axi4_stream_if #(
    parameter int DATA_WIDTH = 32
    /*parameter int ID_WIDTH = 4,
    parameter int DEST_WIDTH = 4,
    parameter int USER_WIDTH = 1*/
) (
    input logic aclk,
    input logic aresetn
);
    logic tvalid;
    logic tready; 
    logic [DATA_WIDTH-1:0] tdata;  
/*    logic [DATA_WIDTH/8-1:0] tstrb; 
    logic [DATA_WIDTH/8-1:0] tkeep;
    logic tlast; 
    logic [ID_WIDTH-1:0] tid;
    logic [DEST_WIDTH-1:0] tdest;
    logic [USER_WIDTH-1:0] tuser;*/

    // AXI requires byte aligned data widths, so confirm compliance here.
    initial begin
        if (DATA_WIDTH % 8 != 0) $fatal(1, $sformatf("AXI DATA_WIDTH=%0d is not byte aligned", DATA_WIDTH));        
    end

    // If using the interface for synthesis, this will probably cause errors. We
    // use it here so we can use `uvm_error in the interface assertion.
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Validate required properties of AXI: once tvalid is asserted, it must remain asserted until
    // tready is asserted.
    assert property (@(posedge aclk) disable iff (!aresetn) $fell(tvalid) |-> $past(tready, 1))
    else `uvm_error("ASSERT", "tvalid must be asserted continuously until tready is asserted.");

endinterface

`endif
