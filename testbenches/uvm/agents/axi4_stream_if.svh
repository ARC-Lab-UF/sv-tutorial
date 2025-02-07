interface axi_stream_if #(
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4,
    parameter DEST_WIDTH = 4,
    parameter USER_WIDTH = 1
) (
    input logic aclk  // Clock signal
);
    logic aresetn;
    logic tvalid;
    logic tready; 
    logic [DATA_WIDTH-1:0] tdata;  
    logic [DATA_WIDTH/8-1:0] tstrb; 
    logic tlast; 
    logic [ID_WIDTH-1:0] tid;
    logic [DEST_WIDTH-1:0] tdest;
    logic [USER_WIDTH-1:0] tuser;

endinterface
