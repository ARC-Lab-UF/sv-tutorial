// Greg Stitt
// University of Florida
// Module: mux_2x1_tb
// Description: This module illustrates a very basic SV testbench for the
// mux2x1 module that uses assertions.

`timescale 1 ns/10 ps 

module mux2x1_tb;

logic in0, in1, sel;
logic out_assign, out_if, out_if2, out_case;
logic correct_out;

// Instantiate the 4 DUTs.
mux2x1_assign DUT_ASSIGN (
    .out(out_assign),
    .*
);
mux2x1_if DUT_IF (
    .out(out_if),
    .*
);
mux2x1_if2 DUT_IF2 (
    .out(out_if2),
    .*
);
mux2x1_case DUT_CASE (
    .out(out_case),
    .*
);

// We use a function here to avoid copying and pasting for the different DUTs
function void check_output(string name, logic actual, logic correct);

      // Use an assertion to check for the correct output. Assertions
      // specify a condition that should always be true.
      // The error message can be printed with different severity levels: 
      // $error, $warning, $fatal, $display
      // Each level can have different behaviors in different simulators.
      // Use $fatal to end the simulation immediately.
      //
      // This assertion is an "immediate" assertion because it occurs within
      // a function (or always block). Concurrent assertions can be used outside
      // of always blocks but require some notion of a clock signal, which isn't
      // appropriate for combinational logic.
      assert(actual == correct) else $error("[%0t] %s = %b instead of %d.", $realtime, name, actual, correct);	 

endfunction

initial begin
    $timeformat(-9, 0, " ns");

    for (int i = 0; i < 8; i++) begin

        in0 <= i[0];
        in1 <= i[1];
        sel <= i[2];
        #10;

        // Verify all the outputs.
        correct_out = sel ? in1 : in0;
        check_output("out_assign", out_assign, correct_out);
        check_output("out_if", out_if, correct_out);
        check_output("out_if2", out_if2, correct_out);
        check_output("out_case", out_case, correct_out);
    end

    $display("Tests completed.");
end
endmodule

