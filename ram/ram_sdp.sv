// Greg Stitt
// StittHub (www.stitt-hub.com)

// Note: This code has not been tested in the non-pro versions of Quartus. 
// SystemVerilog support is not great in those versions, so I have abandonded 
// trying to support it.

// The following module provides standard single dual-port RAM behavior that
// is supported by most FPGAs. Some FPGAs use block RAMs that don't directly 
// support an read enable, but they can implement it with extra logic. If you
// don't need the read enable, simply set it to 1 when you instantiate this
// module and this should synthesize directly onto RAM resources in most FPGAs.
//
// One important thing to note is that this provides a "read-first" read-during-write
// behavior. In other words, when the read port and and write port use the same
// address, the read returns the old data, not the data currently being written.

module ram_sdp_basic #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data <= ram[rd_addr];
    end
endmodule


// The following module demonstrates one way of implementing a "write-first" 
// read-during-write behavior. I do not recommend this style. First, in Vivado,
// it doesn't work with block RAM or UltraRAM. Second, it works in Quartus, but
// causes it to infer extra "pass-through" or "bypassing" logic. If you need
// write-first behavior, you'll need that logic, but I'll show you how to do it
// in a way that works on all FPGAs. Finally, even if you are only using Quartus,
// it comes with risks. There is a setting in Quartus to disable inference of
// this pass-through logic. The problem is that your design will still compile
// with the pass-through logic disable without any errors, but it won't work on
// the actual FPGA because it won't provide a write-first behavior. I wasted 
// weeks of my life debugging this, so I always implement my own logic for 
// write-first. Finally, this code violates most style guidelines because the
// blocking assignment on a clock edge is a common cause of race conditions.

module ram_sdp_write_first_inferred #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    always_ff @(posedge clk) begin
        // The blocking assignment causes a read from the same address to get 
        // the new data.
        if (wr_en) ram[wr_addr] = wr_data;
        if (rd_en) rd_data <= ram[rd_addr];
    end
endmodule


// The following module demonstrates my suggested manual logic for implementing
// write-first behavior.

module ram_sdp_write_first_manual #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;
    logic bypass_valid_r = 1'b0;
    logic [DATA_WIDTH-1:0] bypass_data_r;

    // Save write data in a register in case of a read-during-write. This 
    // register "bypasses" the read from RAM to provide the new write data.    
    always_ff @(posedge clk) begin
        if (rd_en && wr_en) bypass_data_r <= wr_data;
        if (rd_en) bypass_valid_r <= wr_en && rd_addr == wr_addr;
    end

    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    // Mux to select from the memory or the bypass register in the event of a
    // read-during-write. 
    assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
endmodule


// This module adds a register read data output, which is very commonly 
// provided by RAM resources across most FPGAs. It is also generally a very good
// idea to register the read data to improve clock frequencies, as the time to
// read from memory creates a long logic delay.
//
// Note that not all FPGAs provide RAMs that support a read enable on the 
// registered output (or even on the read port at all). This template still 
// works on those FPGAs, but the register simply won't be packed into the RAM
// primitive. This is easy to check for your FPGAs. Synthesize the design and 
// look at the resource counts, or the schematic. If the register is packed into
// the RAM resource, there will be no registers used in your design. If it isn't
// packed into the RAM resource, you will see registers in the resource counts,
// and in the schematic.
//
// Like the basic template, if you don't need the read enable, just connect it
// to 1'b1 when you instantiate it, and the output register should be packed
// on most FPGAs.

module ram_sdp_output_reg #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
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


// In this module, we combine all the above functionality into a single, 
// generalized module with parameters that control each option.
//
// This module should work well across most FPGAs. It's only big limitation is
// that it doesn't give us control over what type of RAM resource to use. FPGAs
// often have multiple RAM types, so we'll add that next.

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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

    // Infer the RAM (always use read-first here)
    always_ff @(posedge clk) begin
        if (wr_en) ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= ram[rd_addr];
    end

    // Add the manual bypassing logic to support write-first.
    if (WRITE_FIRST) begin : l_write_first
        // We don't have a reset in this template, so we'll make sure the valid
        // register is initialized to 0 after the bitstream is loaded.
        logic bypass_valid_r = 1'b0;
        logic [DATA_WIDTH-1:0] bypass_data_r;

        always_ff @(posedge clk) begin
            if (rd_en && wr_en) bypass_data_r <= wr_data;
            if (rd_en) bypass_valid_r <= wr_en && rd_addr == wr_addr;
        end

        // Add the optional registered read port if requested.
        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= bypass_valid_r ? bypass_data_r : rd_data_ram;
        end else begin : l_no_reg_rd_data
            assign rd_data = bypass_valid_r ? bypass_data_r : rd_data_ram;
        end
    end else begin : l_read_first
        // Add the optional registered read port if requested.
        if (REG_RD_DATA) begin : l_reg_rd_data
            always_ff @(posedge clk) if (rd_en) rd_data <= rd_data_ram;
        end else begin : l_no_reg_rd_data
            assign rd_data = rd_data_ram;
        end
    end
endmodule


// The following module shows how to specialize the SDP template for Quartus and
// Intel/Altera FPGAs. This ideally should work in Vivado also, but Vivado has
// a longstanding bug that requires a workaround that I show later.
//
// This module adds a STYLE parameter, which uses a string to specify the 
// specific type of RAM resource. See the documentation for your specific FPGA
// to see the supported types. You can leave as the default to let the synthesis
// tool choose.
//
// As mentioned before, you will probably want to set the read enable to 1 when
// you instantiate this template if you want a single RAM resource without any
// extra logic. However, the read enable will still work correctly, just with
// extra logic surrounding the RAM.

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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
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


// The following module demonstrates the workaround to get the STYLE parameter
// working in Vivado. Hopefully the bug will be fixed in future versions, 
// allowing this template to be merged with the previous one.

module ram_sdp_vivado1 #(
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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    // Unlike Quartus, Vivado uses ram_style instead of ramstyle. 
    // Ideally, we would imitate the previous this previous code:
    //
    //(* ram_style = STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];

    // However, but Vivado has a bug preventing anything but string literals 
    // from being used in attributes. So, we can hardcode a string literal, but
    // that doesn't give us the flexibility to support different styles via a
    // parameter.

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
        // To make the earlier workaround work, we need a few small changes here.
        // The ram signal has a scope that's only visible within its if-generate
        // region, so to access it from outside that scope, we need to use a 
        // prefix with the generate label l_ram.
        if (wr_en) l_ram.ram[wr_addr] <= wr_data;
        if (rd_en) rd_data_ram <= l_ram.ram[rd_addr];
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


module ram_sdp_vivado_attempt1 #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter logic [8*16-1:0] STYLE = ""
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    // Fix attempt 1: simply use the logic array in place of the previous string.
    (* ram_style = STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

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


module ram_sdp_vivado_attempt2 #(
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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    //localparam logic [8*16-1:0] MEM_STYLE = STYLE;
    //(* ram_style = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    (* ram_style = STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

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


module ram_sdp_vivado_attempt3 #(
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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    localparam int MAX_STYLE_LEN = 16;
    typedef logic [MAX_STYLE_LEN*8-1:0] string_as_logic_t;
    localparam logic [MAX_STYLE_LEN*8-1:0] MEM_STYLE = string_as_logic_t'(STYLE);

    (* ram_style = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

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


module ram_sdp_vivado_quartus #(
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
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);
    localparam int MAX_STYLE_LEN = 16;
    typedef logic [MAX_STYLE_LEN*8-1:0] string_as_logic_t;
    localparam logic [MAX_STYLE_LEN*8-1:0] MEM_STYLE = string_as_logic_t'(STYLE);

    (* ram_style = MEM_STYLE, ramstyle = MEM_STYLE *) logic [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram;

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


// Change the ARCH string in the following module to synthesize or simulate
// different versions of the RAM.

module ram_sdp #(
    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 10,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "MLAB",
    parameter string ARCH = "vivado_quartus"
) (
    input  logic                  clk,
    input  logic                  rd_en,
    input  logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data,
    input  logic                  wr_en,
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
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
    end else if (ARCH == "vivado1") begin : l_vivado1
        ram_sdp_vivado1 #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end else if (ARCH == "vivado_attempt1") begin : l_vivado2
        ram_sdp_vivado_attempt1 #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
            //.STYLE      ("block")
        ) ram (
            .*
        );
    end else if (ARCH == "vivado_attempt2") begin : l_vivado2
        ram_sdp_vivado_attempt2 #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            //.STYLE      ("block")
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end else if (ARCH == "vivado_attempt3") begin : l_vivado_final
        ram_sdp_vivado_attempt3 #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end else if (ARCH == "vivado_quartus") begin : l_vivado_quartus
        ram_sdp_vivado_quartus #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) ram (
            .*
        );
    end else begin : l_error
        $fatal(1, "Illegal ARCH %0s for ram_sdp", ARCH);
    end

endmodule
