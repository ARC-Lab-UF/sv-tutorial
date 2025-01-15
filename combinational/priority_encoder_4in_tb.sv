// Greg Stitt
// University of Florida

`timescale 1ns / 100 ps

// Module: priority_encoder_4in_tb
// Description: A simple testbench for the priority_encoder_4in module.

module priority_encoder_4in_tb;

    logic [3:0] inputs;
    logic [1:0] result;
    logic       valid;

    priority_encoder_4in DUT (.*);

    initial begin
        logic [1:0] correct_result;
        logic       correct_valid;
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 16; i++) begin
            inputs = i;
            #10;

            correct_result = '0;
            for (int j = 3; j >= 0; j--) begin
                if (inputs[j] == 1'b1) begin
                    correct_result = j;
                    break;
                end
            end

            correct_valid = inputs != 4'b0;

            if (result != correct_result)
                $display("ERROR (time %0t): result = %b instead of %b.", $realtime, result, correct_result);

            if (valid != correct_valid)
                $display("ERROR (time %0t): valid = %b instead of %b.", $realtime, valid, correct_valid);
        end

        $display("Tests completed.");
    end
endmodule

