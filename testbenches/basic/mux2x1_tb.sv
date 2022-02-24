// Greg Stitt
// University of Florida
// Description: This file illustrates two testbenches. The first is a very 
// basic SV testbench for the mux2x1 module. The second demonstrates how to
// test multiple modules that should behave identically.

// Verilog uses metricless time literals (e.g. #20), which requires
// this extra timescale information for the simulator to work.
// The first value is time unit (e.g. for 1 ns, #20 = 20 ns)
// The second value is the precision for rounding: 
// e.g. for 1ns/1ns, #0.42 = 0 ns.
// for 1ns/1ns, #0.65 = 1ns.
// See the following for more detail:
// https://www.chipverify.com/verilog/verilog-timescale
`timescale 1 ns/10 ps // 1 ns time unit, 10 ps precision

// Module: mux2x1_tb
// Description: This module is a basic testbench for the mux2x1 module. It is
// intended to be an intro tutorial to the basic constructs and tools used in
// testbenches.

// The testbench is just a module with no I/O.
module mux2x1_tb;

   // Declare local logic for I/O. I highly suggest using the same name as the 
   // module's I/O when possible to simplify the port connections.
   logic in0, in1, sel, out;

   // Variable to store the correct output for comparison.
   logic correct_out;           
  
   // Define a period of time between tests. Uses specified timescale (ns).
   localparam period = 20;
   
   // Instantiate the module we want to test. The typical SV naming convention
   // is DUT for design under test.
   mux2x1 DUT (.*);

   // Initial is like an always block that only runs once. It is appropriate
   // for a set of tests that run once.
   initial
     begin
        // When we print messages later on, we will want to display the time.
        // If we don't specify the format, the time won't have any units,
        // and we won't be able to move the cursor to a message in a simulator
        // GUI. In this example, we set the time units to nanosecond scale.
        //
        // See following for formatting:
        // https://www.chipverify.com/verilog/verilog-timeformat
        $timeformat(-9, 0, " ns");
        
        // Loop over all possible combinations of inputs.       
        for (integer i=0; i < 8; i = i+1) begin
           
           // Index into the loop counter bits to assign individual inputs.
           in0 = i[0];
           in1 = i[1];
           sel = i[2];

           // Wait for the specified amount of time.
           #period;

           // Check for correct output.
           correct_out = sel ? in1 : in0;
           if (correct_out != out)
             // See following for formatting of $display:
             // https://www.chipverify.com/verilog/verilog-display-tasks
             $display("ERROR at time %0t: out = %b instead of %d.", $realtime, out, correct_out);           
        end

        $display("Tests completed.");
     end 
endmodule


// Most testbenches test a single DUT, but here is an example of testing
// multipe DUTs that should all behave the same.
module mux2x1_all_tb;

   logic in0, in1, sel;
   
   // We have four modules to test, so we need four outputs.
   logic out_assign, out_if, out_if2, out_case;   

   logic correct_out;           
   
   localparam period = 20;
   
   // Instantiate the 4 DUTs.
   mux2x1_assign DUT_ASSIGN (.out(out_assign), .*);
   mux2x1_if DUT_IF (.out(out_if), .*);
   mux2x1_if2 DUT_IF2 (.out(out_if2), .*);
   mux2x1_case DUT_CASE (.out(out_case), .*);

   // We use a function here to avoid copying and pasting for the different LUTs
   function void check_output(string name, logic actual, logic correct);
      if (actual != correct) begin       
     
         $display("ERROR at time %0t: %s = %b instead of %d.", $realtime, name, actual, correct);
      end
   endfunction

   initial begin
      $timeformat(-9, 0, " ns");
      
      for (integer i=0; i < 8; i = i+1) begin
      
         in0 = i[0];
         in1 = i[1];
         sel = i[2];
         #period;
         
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
