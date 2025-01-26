// Greg Stitt
// University of Florida

module delay #(
    parameter int CYCLES = 8,
    parameter int WIDTH  = 16
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    initial begin
        if (CYCLES < 0) $fatal(1, "Cycles must be positive.");
        if (WIDTH < 1) $fatal(1, "Width must be >= 1");
    end

    generate
        if (CYCLES == 0) begin : no_delay_l
            assign data_out = data_in;
        end else begin : delay_l
            logic [WIDTH-1:0] delay_r[CYCLES];

            always_ff @(posedge clk or posedge rst) begin
                if (rst) begin
                    delay_r <= '{default: '0};
                end else if (en) begin
                    delay_r[0] <= data_in;
                    for (int i = 1; i < CYCLES; i++) delay_r[i] <= delay_r[i-1];
                end
            end

            assign data_out = delay_r[CYCLES-1];
        end
    endgenerate
endmodule
