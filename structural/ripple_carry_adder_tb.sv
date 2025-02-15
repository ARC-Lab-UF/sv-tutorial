// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

module ripple_carry_adder_tb;

    localparam int NUM_TESTS = 1000;
    localparam int WIDTH = 8;
    logic [WIDTH-1:0] x, y, sum, correct_sum;
    logic cin, cout, correct_cout;

    ripple_carry_adder UUT (.*);

    initial begin
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < NUM_TESTS; i++) begin
            x   <= $urandom;
            y   <= $urandom;
            cin <= $urandom;
            #10;
            {correct_cout, correct_sum} = x + y + cin;
            if (sum != correct_sum)
                $display("ERROR (time %0t): sum = %d instead of %d.", $realtime, sum, correct_sum);

            if (cout != correct_cout)
                $display("ERROR (time %0t): cout = %b instead of %b.", $realtime, cout, correct_cout);
        end

        $display("Tests completed.");
    end

endmodule  // ripple_carry_adder_tb
