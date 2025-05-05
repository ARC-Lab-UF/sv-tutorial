// Greg Stitt
// University of Florida

module ram_sdp_basic #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data <= ram[rd_addr];
    end
endmodule


module ram_sdp_write_first_inferred #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);

    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    always_ff @(posedge clk) begin
        // The blocking assignment here causes the read to get the new data.
        if (wr_en) ram[wr_addr] = wr_data;
        if (rd_en) rd_data <= ram[rd_addr];
    end
endmodule


module ram_sdp_write_first_manual #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;
    logic bypass_valid_r = 1'b0;
    logic [DATA_WIDTH-1:0] bypass_data_r;

    // Save write data in a register in case of a read-during-write. The write 
    // data is then used on the read output to "bypass" the RAM's read data.
    always_ff @(posedge clk) begin
        if (rd_en && wr_en) begin
            bypass_data_r  <= wr_data;
            bypass_valid_r <= rd_addr == wr_addr;
        end
    end

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    // Include a mux on the 
    assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
endmodule


module ram_sdp_output_reg #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    always_ff @(posedge clk) begin
        if (rd_en) rd_data <= rd_data_ram;
    end
endmodule


module ram_sdp_general #(
    parameter int DATA_WIDTH  = 16,
    parameter int ADDR_WIDTH  = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    if (WRITE_FIRST) begin : write_first
        logic bypass_valid_r = 1'b0;
        logic [DATA_WIDTH-1:0] bypass_data_r;

        always_ff @(posedge clk) begin
            if (rd_en && wr_en) begin
                bypass_data_r  <= wr_data;
                bypass_valid_r <= rd_addr == wr_addr;
            end
        end

        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : read_first
        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule


module ram_sdp_quartus #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = ""
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    // Quartus uses the "ramstyle" attribute to control what type of RAM resource
    // is inferred. The acceptable values vary across FPGAs, but are usually 
    // "M4K", "M9K", "M20K", "M144k", and "MLAB".
    (* ramstyle = STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    if (WRITE_FIRST) begin : write_first
        logic bypass_valid_r = 1'b0;
        logic [DATA_WIDTH-1:0] bypass_data_r;

        always_ff @(posedge clk) begin
            /*if (rd_en && wr_en) begin
                bypass_data_r  <= wr_data;
                bypass_valid_r <= rd_addr == wr_addr;
            end*/
            if (rd_en && wr_en) bypass_data_r <= wr_data;
            if (rd_en) bypass_valid_r <= wr_en && rd_addr == wr_addr;
        end

        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : read_first
        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule


module ram_sdp_vivado #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "auto"
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);
    // Unlike Quartus, Vivado uses ram_style instead of ramstyle. 
    // Ideally, we would just do this, but Vivado has a bug preventing anything
    // but string literals from being used in attributes.
    //(* ram_style = STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    // Strangely, the following works in Vivado, but doesn't in most simulators:
    //(* ram_style = $sformatf("%s", STYLE) *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    // An ugly workaround is to manually specify each possible attribute:
    if (STYLE == "block") begin : l_ram
        (* ram_style = "block" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else if (STYLE == "distributed") begin : l_ram
        (* ram_style = "distributed" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    end else if (STYLE == "registers") begin : l_ram
        (* ram_style = "registers" *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
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

    logic [DATA_WIDTH-1:0] rd_data_ram;

    always_ff @(posedge clk) begin
        // The ram signal has a scope that's only visible within its if-generate,
        // so to access it from outside that scope, we need to use a prefix with
        // the generate label l_ram.
        if (wr_en) l_ram.ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= l_ram.ram[rd_addr];
    end

    if (WRITE_FIRST) begin : write_first
        logic bypass_valid_r = 1'b0;
        logic [DATA_WIDTH-1:0] bypass_data_r;

        always_ff @(posedge clk) begin
            if (rd_en && wr_en) begin
                bypass_data_r  <= wr_data;
                bypass_valid_r <= rd_addr == wr_addr;
            end
        end

        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : read_first
        if (REG_RD_DATA) begin : reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= rd_data_ram;
        end else begin : no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule


module ram_sdp #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b1,
    parameter bit WRITE_FIRST = 1'b1,
    parameter string STYLE = "",
    parameter string ARCH = "quartus"
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,

    input logic                  wr_en,
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data
);

    if (ARCH == "basic") begin : l_basic
        ram_sdp_basic #(
            .DATA_WIDTH(DATA_WIDTH),
            .ADDR_WIDTH(ADDR_WIDTH)
        ) ram (
            .*
        );
    end else if (ARCH == "write_first_inferred") begin : l_write_first_inferred
        ram_sdp_write_first_inferred #(
            .DATA_WIDTH(DATA_WIDTH),
            .ADDR_WIDTH(ADDR_WIDTH)
        ) ram (
            .*
        );
    end else if (ARCH == "write_first_manual") begin : l_write_first_manual
        ram_sdp_write_first_inferred #(
            .DATA_WIDTH(DATA_WIDTH),
            .ADDR_WIDTH(ADDR_WIDTH)
        ) ram (
            .*
        );
    end else if (ARCH == "output_reg") begin : l_output_reg
        ram_sdp_output_reg #(
            .DATA_WIDTH(DATA_WIDTH),
            .ADDR_WIDTH(ADDR_WIDTH)
        ) ram (
            .*
        );

    end else if (ARCH == "general") begin : l_general
        ram_sdp_general #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST)
        ) ram (
            .*
        );
    end else if (ARCH == "quartus") begin : l_quartus
        ram_sdp_quartus #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end else if (ARCH == "vivado") begin : l_vivado
        ram_sdp_vivado #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end

endmodule
