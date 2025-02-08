module mult #(
    parameter int INPUT_WIDTH = 8
) (
    input logic aclk,
    input logic arst_n,

    // AXI4 stream interface for each multiplier input.
    input  logic                   in_tvalid[2],
    output logic                   in_tready[2],
    input  logic [INPUT_WIDTH-1:0] in_tdata [2],

    // AXI4 stream interface for multiplier output
    output logic                     out_tvalid,
    input  logic                     out_tready,
    output logic [2*INPUT_WIDTH-1:0] out_tdata
);

    logic [INPUT_WIDTH-1:0] in_r[2];
    logic [1:0] in_valid_r;
    logic en;
    logic [INPUT_WIDTH*2-1:0] product_r;
    logic product_valid_r;

    // Enable/disable the pipeline with the output interface's tready.
    assign en = out_tready;

    // Clear ready on an input port if there is a valid input on the
    // port and an invalid input of the other port. I.e., we need to wait for
    // both ports to have data before continuing.
    assign in_tready[0] = en && !(in_valid_r[0] && !in_valid_r[1]);
    assign in_tready[1] = en && !(in_valid_r[1] && !in_valid_r[0]);

    always_ff @(posedge aclk) begin
        if (en) begin
            in_valid_r[0] <= in_tvalid[0];
            if (in_tvalid[0]) in_r[0] <= in_tdata[0];

            in_valid_r[1] <= in_tvalid[1];
            if (in_tvalid[1]) in_r[1] <= in_tdata[1];

            product_r <= in_r[0] * in_r[1];
            product_valid_r <= &in_valid_r;
        end

        if (!arst_n) begin
            in_valid_r <= '0;
            product_valid_r <= 1'b0;
        end
    end

    assign out_tvalid = product_valid_r;
    assign out_tdata  = product_r;

endmodule
