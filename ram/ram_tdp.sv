// Greg Stitt
// StittHub (www.stitt-hub.com)

// The following shows a somewhat reusable true dual-port (TDP) RAM template.
// It works on some Xilinx/AMD and Intel/Altera FPGAs, as long as you don't need
// to specify the specific RAM resource, which I add in other examples.
//
// The tricky part of creating a reusable TDP template is that different FPGAs,
// even those from the same vendor, and even those within the same FPGA, can 
// provide variations of behavior. In my attempt at a unified template, I
// explored the commonality across most FPGAs.
//
// It is very important to understand the exact TDP behaviors of your specific
// FPGA. Some FPGAs prohibit certain actions (e.g., reading from one port and
// writing to another port using the same address). If you don't comply with
// those requirements, you can get undefined behaviors. As added protection, I
// usually supplement this template with assertions that check for prohibited
// behaviors on my targeted FPGA.
//
// In addition, different RAM resources might provide unique behaviors that are
// ommitted from this template, but can be quite useful.
//
// Note that there is no WRITE_FIRST parameter here. I omitted it because of 
// wide differences of read-during-write behaviors on different FPGAs.
//
// Note: This has not been tested in the non-pro versions of Quartus. 
// SystemVerilog support is not great in those versions, so I have abandoned 
// trying to support it.

module ram_tdp #(
    parameter int DATA_WIDTH  = 4,
    parameter int ADDR_WIDTH  = 8,
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
    // Apply the Vivado STYLE workaround from the SDP module. This isn't needed
    // if you are only using Quartus.
    localparam int MAX_STYLE_LEN = 16;
    typedef logic [MAX_STYLE_LEN*8-1:0] string_as_logic_t;
    localparam logic [MAX_STYLE_LEN*8-1:0] MEM_STYLE = string_as_logic_t'(STYLE);

    // Set ram_style for Vivado and ramstyle for Quartus.
    (* ram_style = MEM_STYLE, ramstyle = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
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
