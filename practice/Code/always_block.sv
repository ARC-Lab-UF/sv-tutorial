`timescale 1ns/1ps
//always may have ssingle or multiple statements
//format--> always @(sensitivity list)
//Types of always block:
//    --> always_comb : for combinational logic
//    --> always_ff : for sequential logic
//    --> always_latch : for latch logic

// for testbench, in the always block, we don't need to specify the sensitivity list
// for combinational logic, sentitivity list is required in always block.
    //ex: always @(a,b) // where a and b are the inputs
// for sequential logic, clock is required in always block. (clk is the sensitive input)
    //ex: always @(posedge clk) // where clk is the clock signal, and the circuit is evaluated
    // on every positive edge of the clock
// But these are only for the circuits, not for the testbench. We don't need to specify the
// sensitivity list for the testbench.
// always block will start at t = 0, and be evaluated till the end of the simulation. Where as the initial block will
// be evaluated only once at the beginning(t=0) of the simulation, execute all the statements 
// inside the initial block and then stop.

// Without a sensitivity list, the always block will be evaluated forever. So we need to do $finish() to stop it.
// Primary use of always: Generate the clock signal

// generate clock signal with 10ns period:
module clk_gen();
reg clk, clk50, clk25, rst;           // by default these will be X. So we need to assign them a value.

initial begin
    clk = 0;
    clk50 = 0;
    clk25 = 0;
    rst = 0;
end
    always #5 clk = ~clk; // #5 means 5ns delay, and ~ means negation // 100 MHz clock
    // in the above statement, #5 is the half clock period.
    always #5 clk50 = ~clk50; // 50 Mhz clock
    always #5 clk25 = ~clk25; // 25 Mhz clock
initial begin
    #200;
    $finish();
end
endmodule



module tb();


endmodule