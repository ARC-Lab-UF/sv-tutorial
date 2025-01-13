// Greg Stitt
// University of Florida
// Module: mux_2x1_tb
// Description: This module illustrates a very basic SV testbench for the
// mux2x1 module.


// Verilog uses metricless time literals (e.g. #20), which requires
// this extra timescale information for the simulator to work.
// The first value is time unit (e.g. for 1 ns, #20 = 20 ns)
// The second value is the precision for rounding: 
// e.g. for 1ns/1ns, #0.42 = 0 ns.
// for 1ns/1ns, #0.65 = 1 ns.
// See the following for more detail:
// https://www.chipverify.com/verilog/verilog-timescale
`timescale 1 ns / 10 ps  // 1 ns time unit, 10 ps precision


// The testbench is just a module with no I/O.
module mux2x1_tb;

    // Declare local logic for I/O. I highly suggest using the same name as the 
    // module's I/O when possible to simplify the port connections.
    logic in0, in1, sel;

    // We have multiple modules to test, so we need multiple outputs.
    logic out_assign, out_if, out_if2, out_if3, out_case;

    // Define a period of time between tests. Uses specified timescale (ns).
    localparam int period = 20;

    // Instantiate the modules we want to test. The typical SV naming convention
    // is DUT for design under test. Here we have 4 DUTs, but most testbenches
    // only have one.
    mux2x1_assign DUT_ASSIGN (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out_assign)
    );
    mux2x1_if DUT_IF (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out_if)
    );
    mux2x1_if2 DUT_IF2 (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(out_if2)
    );
    mux2x1_if2 DUT_IF3 (
      .in0(in0),
      .in1(in1),
      .sel(sel),
      .out(out_if3)
  );
    mux2x1_case DUT_CASE (
        .out(out_case),

        // .* establishes connections with signals that have the same name as the
        // I/O on the port of the module, that have not explicitly been connected.
        // Many people consider this to be a bad practice since it hides the
        // details of the port. I personally only use it in testbenches where my
        // convention is to always use signals with the same name as the I/O.
        .*
    );

    // Check to see if the output is correct and print an error message if not.
    function void check_output(string name, logic actual, logic correct);
        if (actual != correct) begin
            $display("ERROR at time %0t: %s = %b instead of %d.", $realtime, name, actual, correct);

            // Or, 
            //$error("Time %0t: %s = %b instead of %d.", $realtime, name, actual, correct);
        end
    endfunction

    logic correct_output;

    // Initial is like an always block that only runs once. It is appropriate
    // for a set of tests that run once, or anything you need to initially run
    // at the beginning of a simulation.
    initial begin
        // See following for formatting of $display and time:
        // https://www.chipverify.com/verilog/verilog-display-tasks
        // https://www.chipverify.com/verilog/verilog-timeformat
        $timeformat(-9, 0, " ns");

        // Loop over all possible combinations of inputs.	
        for (integer i = 0; i < 8; i = i + 1) begin

            // Index into the loop counter bits to assign individual inputs.
            in0 = i[0];
            in1 = i[1];
            sel = i[2];

            // Wait for the specified amount of time.
            #period;

            // Check for correct outputs.
            correct_output = sel ? in1 : in0;
            check_output("out_assign", out_assign, correct_output);
            check_output("out_if", out_if, correct_output);
            check_output("out_if2", out_if2, correct_output);
            check_output("out_if3", out_if3, correct_output);
            check_output("out_case", out_case, correct_output);
        end
    end
endmodule
