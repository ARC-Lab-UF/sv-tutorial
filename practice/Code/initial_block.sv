/*3 types of signals:
	• Global 
		○ Clk, rst
	• Control
		○ Wr, rd, raddr, waddr
	• Data
		○ Rdata, wdata
*/
`timescale 1ns/1ps
//Initial Block:
// Uses are as follows:
// 1. Initialixe global variables
// 2. Generate random values for data/signals for simulation
// 3. Run system tasks at the start of simulation(eg: dump vcd file)
// 4. Stop simulation after a certain time by forcefully calling finish()

module tb (); //testbench does not have any ports ideally 
	reg clk;
    reg rst;
    reg a = 0;
    reg [3:0] temp;
// Initial blocks always start executing at the start of the simulation, at time t = 0;
	initial begin
		a = 1;
		#10;
		a = 0;
	end  
// global signals clk and rst
    initial begin
		clk = 1'b0;
		rst = 1'b0;
	end    
    initial begin
        temp = 4'b0100;
        #10;
        temp = 4'b0010;
    end
// generate a vcd file:
    initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    end
// end simulation by calling finish()
    initial begin
        #200;
        $finish();
    end
endmodule


