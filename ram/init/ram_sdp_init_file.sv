// Greg Stitt
// StittHub (www.stitt-hub.com)

module ram_sdp_init_file #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "",
    parameter string INIT = ""
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    // Use a Vivado workaround to enable string parameter for ram_style.
    localparam int MAX_STYLE_LEN = 16;
    typedef logic [MAX_STYLE_LEN*8-1:0] string_as_logic_t;
    localparam logic [MAX_STYLE_LEN*8-1:0] MEM_STYLE = string_as_logic_t'(STYLE);

    // Specify ram_style for Vivado, and ramstyle for Quartus.
    (* ram_style = MEM_STYLE, ramstyle = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    // Read the contents of the INIT file into the RAM array.
    initial begin
        $readmemh(INIT, ram);
    end

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    if (WRITE_FIRST) begin : l_write_first
        logic bypass_valid_r = 1'b0;
        logic [DATA_WIDTH-1:0] bypass_data_r;

        always_ff @(posedge clk) begin
            if (rd_en && wr_en) bypass_data_r <= wr_data;
            if (rd_en) bypass_valid_r <= wr_en && rd_addr == wr_addr;
        end

        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;
        end else begin : l_no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : l_read_first
        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= rd_data_ram;
        end else begin : l_no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule
