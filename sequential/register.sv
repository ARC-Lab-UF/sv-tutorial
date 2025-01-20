// Greg Stitt
// University of Florida
//
// This example illustrates a variety of different register modules. To simulate
// a different module, change the comments in the register module at the bottom
// of this file.

// Module: register_async_rst
// Description: Implements a register with an active high, asynchronous reset.

module register_async_rst #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // Sequential logic should usually use the always_ff block. You can use an
    // normal always block, but always_ff enables tools to apply additional 
    // checks that ensure that every assignment synthesizes to flip-flops. In
    // my experience, tools do not really verify flip flops, but instead just
    // report warnings about blocking assignments being used. Blocking assignments
    // *can* synthesize to flip-flops (see other tutorial examples), but
    // non-blocking assignments on clock edges *always* synthesize to flip-flops.
    // My other tutorial examples will show situations that are safe to mix 
    // non-blocking and blocking assignments.

    // For a register with an asynchronous reset, we want to update the output
    // on any rising clock edge or reset edge.
    always_ff @(posedge clk or posedge rst) begin

        // Checking reset first gives it priority over the clock edge, which is
        // what we want for an asynchronous reset.
        if (rst) out <= '0;
        else begin
            // This else corresponds to anything on a rising clock edge.
            // SYNTHESIS RULE: Any non-blocking assignment on a rising clock edge
            // will synthesize into a register. Blocking assignments can be mixed
            // with non-blocking assignments, but will cause warnings in always_ff
            // blocks because they don't always synthesize to a register.
            out <= in;
        end
    end
endmodule  // register_async_rst


// Module: register_async_rst2
// Description: Implements a register with an active high, asynchronous reset using
// a different coding style for the reset.

module register_async_rst2 #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    always_ff @(posedge clk or posedge rst) begin

        out <= in;

        // Another reset style is putting the reset check at the end of the 
        // always block. With this style, any prior assignment to out is 
        // simply reassigned if the reset is asserted. This style can have 
        // significant benefits in some situations that will be explained
        // in later examples.
        if (rst) out <= '0;
    end
endmodule  // register_async_rst2


// Module: register_sync_rst
// Description: Implements a register with an active high, synchronous reset.

module register_sync_rst #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // For a synchronous reset, we only want to update output on a clock edge.
    always_ff @(posedge clk) begin
        // The inside of all the always block is identical, but now the reset is
        // synchronous because this if statement will only ever happen on a clock
        // edge.
        if (rst) out <= '0;
        else out <= in;
    end
endmodule  // register_sync_rst


// Module: register_sync_rst2
// Description: Implements a register with an active high, synchronous reset using
// an alternative coding style for reset.

module register_sync_rst2 #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // For a synchronous reset, we only want to update output on a clock edge.
    always_ff @(posedge clk) begin
        out <= in;

        // Alternative reset style at the end of the block.
        if (rst) out <= '0;
    end
endmodule  // register_sync_rst2


// Module: register_en_async_rst
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register_en_async_rst #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);

    always_ff @(posedge clk or posedge rst) begin
        if (rst) out <= '0;

        // Registers typically have an enable or a load signal which must be
        // asserted for the output to change. We can implement this by simply
        // checking if the enable is asserted on a rising clock edge.
        else if (en) out <= in;
    end

endmodule  // register_en_async_rst


// Module: register_en_async_rst2
// Description: Modifies the previous register with an alternative reset coding style.

module register_en_async_rst2 #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);

    always_ff @(posedge clk or posedge rst) begin
        if (en) out <= in;

        // End-of-block resets still work with additional register functionality.
        if (rst) out <= '0;
    end

endmodule  // register_en_async_rst2


// Module: register_en_sync_rst
// Description: Implements a register with an active high, ssynchronous reset
// and an enable signal.

module register_en_sync_rst #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // Identical to async reset with posedge rst removed from sensitivity list.
    always_ff @(posedge clk) begin
        if (rst) out <= '0;
        else if (en) out <= in;
    end

endmodule  // register_en_sync_rst


// Module: register_en_sync_rst2
// Description: Modifies previous module with end-of-block reset coding style.

module register_en_sync_rst2 #(
    parameter int WIDTH
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    always_ff @(posedge clk) begin
        if (en) out <= in;
        if (rst) out <= '0;
    end

endmodule  // register_en_sync_rst2


// Module: register_flexible
// Description: Implements a parameterized register with a configuration 
// parameters for width, type of reset, reset activation level, and reset value.

module register_flexible #(
    parameter int WIDTH = 16,
    parameter logic HAS_ASYNC_RESET = 1'b1,
    parameter logic RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // Uses generate statements to allow for a fully parameterized register.
    // Generally, this much parameterization for sequential logic becomes
    // cumbersome and error prone because of copying and pasting.
    // When targetting FPGAs, I suggest using asynchronous resets in most cases
    // since they tend to use fewer resources than synchronous resets. The exception
    // is when an FPGA's flip-flop resources natively support synchronous resets,
    // in which case it is safer to use synchronous resets.
    //
    // For activation levels, one small disadvantage of parameterization is that
    // the name of the reset signal can't specify the activation level (e.g.
    // rst_n vs rst).
    //
    // In addition, another disadvantage of this much parameterization is that it
    // complicates testing and verification.
    //
    // As an alternative to these generates, there are also preprocessor alternatives
    // that can globally change the reset type of always_ff blocks.
    generate
        if (HAS_ASYNC_RESET) begin : async_l
            if (RESET_ACTIVATION_LEVEL) begin : async_high_l
                // Create an active high async reset.
                always_ff @(posedge clk or posedge rst) begin
                    // Explicitly check the activation level of the reset to support
                    // active high or low.
                    if (rst == RESET_ACTIVATION_LEVEL) out <= RESET_VALUE;
                    else if (en) out <= in;
                end
            end else begin : async_low_l
                // Create an active low async reset.
                always_ff @(posedge clk or negedge rst) begin
                    if (rst == RESET_ACTIVATION_LEVEL) out <= RESET_VALUE;
                    else if (en) out <= in;
                end
            end
        end else begin : sync_l
            // Create an sync reset.
            always_ff @(posedge clk) begin
                if (rst == RESET_ACTIVATION_LEVEL) out <= RESET_VALUE;
                else if (en) out <= in;
            end
        end
    endgenerate
endmodule


module register #(
    parameter int WIDTH = 32,

    // MAKE SURE TO UPDATE THESE FOR EACH MODULE SO THE TESTBENCH
    // FUNCTIONALITY MATHCES
    parameter logic USE_ENABLE = 1'b1,
    parameter logic USE_ASYNC_RST = 1'b0
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    //register_async_rst #(.WIDTH(WIDTH)) top (.*);
    //register_async_rst2 #(.WIDTH(WIDTH)) top (.*);

    //register_sync_rst #(.WIDTH(WIDTH)) top (.*);
    //register_sync_rst2 #(.WIDTH(WIDTH)) top (.*);

    //register_en_async_rst #(.WIDTH(WIDTH)) top (.*);
    //register_en_async_rst2 #(.WIDTH(WIDTH)) top (.*);

    //register_en_sync_rst #(.WIDTH(WIDTH)) top (.*);
    register_en_sync_rst2 #(.WIDTH(WIDTH)) top (.*);

    /*register_flexible #(.WIDTH(WIDTH)) top (.*);*/


endmodule
