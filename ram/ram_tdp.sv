// Greg Stitt
// StittHub (www.stitt-hub.com)

// The following module works on some Xilinx/AMD and Intel/Altera FPGAs, as 
// long as you don't need to specify the specific RAM resource.
//
// Note: This has not been tested in the non-pro versions of Quartus. 
// SystemVerilog support is not great in those versions, so I have abandonded 
// trying to support it.

module ram_tdp #(
    parameter int DATA_WIDTH  = 4,
    parameter int ADDR_WIDTH  = 8,
    parameter bit REG_RD_DATA = 1'b1
) (
    input logic clk,

    // Port A
    input  logic                  en_a,
    input  logic                  wr_en_a,
    input  logic [ADDR_WIDTH-1:0] addr_a,
    input  logic [DATA_WIDTH-1:0] wr_data_a,
    output logic [DATA_WIDTH-1:0] rd_data_a,

    // Port B
    input  logic                  en_b,
    input  logic                  wr_en_b,
    input  logic [ADDR_WIDTH-1:0] addr_b,
    input  logic [DATA_WIDTH-1:0] wr_data_b,
    output logic [DATA_WIDTH-1:0] rd_data_b
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram_a, rd_data_ram_b;

    always @(posedge clk) begin
        if (en_a) begin
            if (wr_en_a) ram[addr_a] <= wr_data_a;
            else rd_data_ram_a <= ram[addr_a];
        end
    end

    always @(posedge clk) begin
        if (en_b) begin
            if (wr_en_b) ram[addr_b] <= wr_data_b;
            else rd_data_ram_b <= ram[addr_b];
        end
    end

    if (REG_RD_DATA) begin : l_reg_rd_data
        always_ff @(posedge clk) begin
            if (en_a) rd_data_a <= rd_data_ram_a;
            if (en_b) rd_data_b <= rd_data_ram_b;
        end
    end else begin : l_no_reg_rd_data
        assign rd_data_a = rd_data_ram_a;
        assign rd_data_b = rd_data_ram_b;
    end
endmodule
