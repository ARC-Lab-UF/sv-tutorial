// Greg Stitt
// University of Florida

// This module implements an AXI4 stream accumulator that accumulates separate
// groups. Each grouop is provided in a packet where the last input in the
// packet is specified by the assertion of tlast.

// Like the previous example, this modules does not "break" the ready signal.
// It chained together with multiple modules that also do not break ready, the
// ready chain will become a timing bottleneck.

module accum #(
    parameter int INPUT_WIDTH  = 16,
    parameter int OUTPUT_WIDTH = 32
) (
    input logic aclk,
    input logic arst_n,

    // AXI4 stream interface for the input.
    input  logic                   in_tvalid,
    output logic                   in_tready,
    input  logic [INPUT_WIDTH-1:0] in_tdata,
    input  logic                   in_tlast,

    // AXI4 stream interface for the output
    output logic                    out_tvalid,
    input  logic                    out_tready,
    output logic [OUTPUT_WIDTH-1:0] out_tdata,
    output logic                    out_tlast
);
    logic en;
    logic out_valid_r;
    logic out_tlast_r;
    logic first_r;
    logic [OUTPUT_WIDTH-1:0] accum_r;

    initial if (INPUT_WIDTH % 8 != 0) $fatal(1, $sformatf("AXI requires INPUT_WIDTH (%0d) to be byte aligned", INPUT_WIDTH));
    initial if (OUTPUT_WIDTH % 8 != 0) $fatal(1, $sformatf("AXI requires OUTPUT_WIDTH (%0d) to be byte aligned", INPUT_WIDTH));

    // Enable/disable the pipeline. AXI streaming is a little weird and can't
    // simply stall on !out_tready. The spec says that a transmitter cannot
    // wait for tready to assert tvalid, so here we enable the pipeline anytime 
    // the output isn't valid. We only stall when !out_tready && out_tvalid.
    assign en = out_tready || !out_tvalid;

    // Ready is combinational logic, which can lead to timing problems. This
    // can easily be fixed with a register and FIFO/skid buffer, which I 
    // avoided to keep the code simple. The main point of the example is to
    // illustrate various UVM concepts.
    assign in_tready = en;

    always_ff @(posedge aclk) begin
        if (en) begin
            out_valid_r <= in_tvalid;
            out_tlast_r <= in_tlast;

            // Don't accumulate unless the input is valid.
            if (in_tvalid) begin
                first_r <= in_tlast;

                // For the first input in a packet, don't add the previous value.
                if (first_r) accum_r <= OUTPUT_WIDTH'(in_tdata);
                else accum_r <= accum_r + OUTPUT_WIDTH'(in_tdata);
            end
        end

        if (!arst_n) begin
            first_r <= 1'b1;
            out_valid_r <= 1'b0;
            out_tlast_r <= 1'b0;
        end
    end

    assign out_tvalid = out_valid_r;
    assign out_tdata  = accum_r;
    assign out_tlast  = out_tlast_r;

endmodule
