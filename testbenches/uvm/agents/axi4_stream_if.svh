`ifndef _AXI4_STREAM_IF_
`define _AXI4_STREAM_IF_

interface axi4_stream_if #(
    parameter DATA_WIDTH = 32
    /*parameter ID_WIDTH   = 4,
    parameter DEST_WIDTH = 4,
    parameter USER_WIDTH = 1*/
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

    initial begin
        if (DATA_WIDTH % 8 != 0) $fatal(1, "AXI DATA_WIDTH must be byte aligned");
    end

endinterface

`endif
