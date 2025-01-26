// Greg Stitt
// University of Florida

// Module: simple_pipeline_with_en
// Description: This module is identical to simple_pipeline, but adds an enable
// that can stall the pipeline.

//===================================================================
// Parameter Description
// WIDTH : The data width (number of bits) of the input and output
//===================================================================

//===================================================================
// Interface Description
// clk  : Clock input
// rst  : Reset input (active high)
// en   : Enable signal (pipeline active when 1, stalled when 0)
// in   : An array of 8 WIDTH-bit inputs
// valid_in : User should assert any time the input data on "in" is valid.
// out  : The output of the multiply accumulate computation.
// valid_out : Asserted whenever "out" contains valid data.
//===================================================================

module simple_pipeline_with_en #(
    parameter int WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] in       [8],
    input  logic             valid_in,
    output logic [WIDTH-1:0] out,
    output logic             valid_out
);
    // Specifies the cycle latency of the pipeline.
    localparam int LATENCY = 4;

    logic [WIDTH-1:0]       in_r[8];
    logic [WIDTH-1:0]       mult_r[4];
    logic [WIDTH-1:0]       add_r[2];
    logic [WIDTH-1:0]       out_r;
    logic [LATENCY-1:0]     valid_delay_r;

    assign out = out_r;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Reset all the registers.
            in_r   <= '{default: '0};
            mult_r <= '{default: '0};
            add_r  <= '{default: '0};
            out_r  <= '0;
        end else begin
            if (en == 1'b1) begin
                // Register the inputs.
                for (int i = 0; i < 8; i++) in_r[i] <= in[i];
                // Perform the multiplications.
                for (int i = 0; i < 4; i++) mult_r[i] <= in_r[i*2] * in_r[i*2+1];
                // Create the first level of adders.
                for (int i = 0; i < 2; i++) add_r[i] <= mult_r[i*2] + mult_r[i*2+1];
                // Create the final adder.
                out_r <= add_r[0] + add_r[1];
            end
        end
    end

    // Delay that determines when out is valid based on the pipeline latency.
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            valid_delay_r <= '{default: '0};
        end else if (en) begin
            valid_delay_r[0] <= valid_in;
            for (int i = 1; i < LATENCY; i++) valid_delay_r[i] <= valid_delay_r[i-1];
        end
    end

    assign valid_out = valid_delay_r[LATENCY-1];
endmodule

