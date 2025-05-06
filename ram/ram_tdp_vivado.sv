// Greg Stitt
// StittHub (www.stitt-hub.com)

module ram_tdp_vivado #(
    parameter int DATA_WIDTH = 4,
    parameter int ADDR_WIDTH = 8,
    parameter bit REG_RD_DATA = 1'b1,
    parameter string STYLE = ""
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
    if (STYLE == "block") begin : l_ram
        (* ram_style = "block" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];    
    end else if (STYLE == "ultra") begin : l_ram
        (* ram_style = "ultra" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else if (STYLE == "mixed") begin : l_ram
        (* ram_style = "mixed" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else if (STYLE == "auto") begin : l_ram
        (* ram_style = "auto" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else if (STYLE == "") begin : l_ram
        logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else begin : l_ram
        initial begin
            $fatal(1, "Invalid STYLE value %s", STYLE);
        end
    end

    logic [DATA_WIDTH-1:0] rd_data_ram_a, rd_data_ram_b;

    // BlockRAM can use different clocks on each port, but UltraRAM can't so
    // we use a single clock to support both.
    always @(posedge clk) begin
        if (en_a) begin
            if (wr_en_a) l_ram.ram[addr_a] <= wr_data_a;
            else rd_data_ram_a <= l_ram.ram[addr_a];
        end
    end

    always @(posedge clk) begin
        if (en_b) begin
            if (wr_en_b) l_ram.ram[addr_b] <= wr_data_b;
            else rd_data_ram_b <= l_ram.ram[addr_b];
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
