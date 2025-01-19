// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: delay_tb
// Description: Testbench for the delay entity. This is a more complicated
// testbench that preserves the correct outputs in an array.

module delay_tb;

    localparam NUM_TESTS = 1000;

    localparam CYCLES = 30;
    localparam WIDTH = 8;
    localparam logic HAS_ASYNC_RESET = 1'b1;
    localparam logic RESET_ACTIVATION_LEVEL = 1'b1;
    localparam logic [WIDTH-1:0] RESET_VALUE = '0;
    logic       clk = 1'b0;
    logic       rst;
    logic       en;
    logic [WIDTH-1:0] in;
    logic [WIDTH-1:0] out;

    delay #(
        .CYCLES                (CYCLES),
        .WIDTH                 (WIDTH),
        .HAS_ASYNC_RESET       (HAS_ASYNC_RESET),
        .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL),
        .RESET_VALUE           (RESET_VALUE)
    ) UUT (
        .*
    );

    initial begin : generate_clock
        while (1) #5 clk = ~clk;
    end

    // Round up the buffer to the next power of 2, which is necessary because
    // of the addressing logic.
    localparam BUFFER_SIZE = 2 ** $clog2(CYCLES);

    // Reset the buffer contents to the reset value.
    logic [WIDTH-1:0] buffer[BUFFER_SIZE] = '{default: RESET_VALUE};

    // Addresses for accessing the buffer. The inputs are written to the buffer
    // and the outputs are read from the buffer.
    logic [$clog2(CYCLES)-1:0] wr_addr = 0;
    logic [$clog2(CYCLES)-1:0] rd_addr;

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst = 1'b1;
        en  = 1'b0;
        in  = '0;
        for (int i = 0; i < 5; i++) @(posedge clk);

        rst = 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            in = $random;
            en = $random;

            // If the delay is enabled, write the new input to it and update
            // the write address.
            if (en) begin
                @(posedge clk);
                wr_addr++;
            end else @(posedge clk);
        end

        // Stop the always blocks.
        disable generate_clock;
        disable check_output;
        $display("Tests completed.");
    end

    logic [WIDTH-1:0] correct_out;
    // The read address should be offset from the write address by CYCLES + 1.
    assign rd_addr = wr_addr - CYCLES + 1;

    initial begin : check_output
        while (1) begin
            @(posedge clk);

            // Check outputs on the falling edge to give time for values to change.
            @(negedge clk);
            if (out != correct_out)
                $display("ERROR (time %0t): out = %h instead of %h.", $realtime, out, correct_out);
        end
    end

    generate
        if (CYCLES == 0) begin
            assign correct_out = in;
        end else begin
            // Imitate a memory with a one-cycle read delay to store the 
            // correct outputs.
            always @(posedge clk, posedge rst) begin
                if (rst) correct_out <= RESET_VALUE;
                else if (en) begin
                    buffer[wr_addr] = in;
                    correct_out <= buffer[rd_addr];
                end
            end
        end
    endgenerate
endmodule  // delay_tb
