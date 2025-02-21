// Greg Stitt
// Wes Piard
// University of Florida

interface axi4_stream_if
    import axi4_stream_pkg::*;
#(
    parameter int DATA_WIDTH = axi4_stream_pkg::DEFAULT_DATA_WIDTH,
    parameter int ID_WIDTH   = axi4_stream_pkg::DEFAULT_ID_WIDTH,
    parameter int DEST_WIDTH = axi4_stream_pkg::DEFAULT_DEST_WIDTH,
    parameter int USER_WIDTH = axi4_stream_pkg::DEFAULT_USER_WIDTH
) (
    input logic aclk,
    input logic aresetn
);
    logic tvalid;
    logic tready;
    logic [DATA_WIDTH-1:0] tdata;
    logic [DATA_WIDTH/8-1:0] tstrb;
    logic [DATA_WIDTH/8-1:0] tkeep;
    logic tlast;
    logic [ID_WIDTH-1:0] tid;
    logic [DEST_WIDTH-1:0] tdest;
    logic [USER_WIDTH-1:0] tuser;

    // AXI requires byte-aligned data widths, so confirm compliance here.
    initial begin
        if (DATA_WIDTH % 8 != 0) $fatal(1, $sformatf("AXI DATA_WIDTH=%0d is not byte aligned", DATA_WIDTH));
    end

    // If using the interface for synthesis, this will probably cause errors.
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Validate required properties of AXI: once tvalid is asserted, it must remain asserted until
    // tready is asserted.
    assert property (@(posedge aclk) disable iff (!aresetn) $fell(tvalid) |-> $past(tready, 1))
    else `uvm_error("ASSERT", "tvalid must be asserted continuously until tready is asserted.");

endinterface
