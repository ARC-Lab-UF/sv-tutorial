// Greg Stitt
// StittHub (www.stitt-hub.com)

module ram_sdp_with_reset #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = ""
) (
    input logic clk,
    input logic rst,

    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    localparam int MAX_STYLE_LEN = 16;
    typedef logic [MAX_STYLE_LEN*8-1:0] string_as_logic_t;
    localparam logic [MAX_STYLE_LEN*8-1:0] MEM_STYLE = string_as_logic_t'(STYLE);

    (* ram_style = MEM_STYLE, ramstyle = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    // IMPORTANT: Make sure to not reset anything here or it likely won't be
    // inferred as a RAM.
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

            // New reset for the write-first logic.
            if (rst) bypass_valid_r <= 1'b0;
        end

        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) begin
                if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;

                // New reset for the registered read data. 
                // IMPORTANT: I would avoid this reset unless absolutely 
                // necessary. Just like some FPGAs don't support a read enable
                // on this register, some don't support a reset at all, some
                // only support an async reset, some only support a sync reset,
                // etc. Your design will always still work with this reset, but
                // it may prevent synthesis from packing the register into the
                // RAM resource. You might not care, but when doing timing
                // optimization, you might need to specialize your template for
                // your specific FPGA. You could also go crazy with more 
                // if-generate combinations, which is something I have in my 
                // personal templates, but I've also been doing this for decades.
                // I don't recommend adding a ton of functionality to your 
                // template until you know you are going to use it.
                if (rst) rd_data <= '0;
            end
        end else begin : l_no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : l_read_first
        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) begin
                if (rd_en) rd_data <= rd_data_ram;

                // New reset for the registered read data. See above comment.
                // I avoid this reset whenever possible.
                if (rst) rd_data <= '0;
            end
        end else begin : l_no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule
