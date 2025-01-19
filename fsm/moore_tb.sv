// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: moore_tb
// Description: Testbench for the moore module, which implements a Moore FSM.
// Note that if moore is changed to use the 1-process version, this testbench
// will start to report errors because of the 1-cycle delay for the outputs.
// It is left as an exercise to adapt the testbench to work for both models.

module moore_tb #(
    parameter int NUM_CYCLES = 1000,

    // Set to 1 for 1-process tests, and 0 for 2-process tests.
    parameter bit DELAY_CORRECT_OUTPUT = 1'b0
);

    logic clk = 0, rst, en;
    logic [3:0] out;

    moore DUT (.*);

    initial begin : generate_clock
        forever #10 clk = ~clk;
    end

    logic [$bits(out)-1:0] correct_out;

    initial begin
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        en <= 1'b0;
        correct_out <= "0001";
        repeat (5) @(posedge clk);

        rst <= 1'b0;

        for (int i = 0; i < NUM_CYCLES; i++) begin
            en <= $random;
            @(posedge clk);
            // The correct output simply rotates every time the enable is asserted.
            if (en) correct_out <= {correct_out[2:0], correct_out[3]};
            
            //if (out != correct_out) $error("[%0t]: out = %h instead of %h.", $realtime, out, correct_out);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    if (DELAY_CORRECT_OUTPUT) begin
        assert property (@(posedge clk) disable iff (rst) out == $past(correct_out, 1))
        else $error("[%0t] out = %h instead of %h.", $realtime, $sampled(out), $past(correct_out, 1));
    end else begin
        assert property (@(posedge clk) out == correct_out)
        else $error("[%0t] out = %h instead of %h.", $realtime, $sampled(out), $past(correct_out, 1));
    end
endmodule
