// Greg Stitt
// StittHub (www.stitt-hub.com)

module ram_init_file_demo #(
    parameter int DATA_WIDTH = 8,
    parameter int ADDR_WIDTH = 6,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "",

    // IMPORTANT: Make sure this path is relative the working directory of your sim/synth project.
    // This can require some experimentation, with some tools not even reporting a
    // warning if the file doesn't exist at the right path.
    parameter string INIT = "ram_init_demo.mem"   
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    ram_sdp_init_file #(
        .DATA_WIDTH (DATA_WIDTH),
        .ADDR_WIDTH (ADDR_WIDTH),
        .REG_RD_DATA(REG_RD_DATA),
        .WRITE_FIRST(WRITE_FIRST),
        .STYLE      (STYLE),
        .INIT       (INIT)
    ) DUT (
        .clk    (clk),
        .rd_en  (rd_en),
        .rd_addr(rd_addr),
        .rd_data(rd_data),
        .wr_en  (wr_en),
        .wr_addr(wr_addr),
        .wr_data(wr_data)
    );

endmodule
