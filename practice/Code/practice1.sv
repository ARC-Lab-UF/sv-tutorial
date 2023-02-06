`timescale 1ns/1ps

module tb_top();
reg clk, rst;

initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    end
  
initial begin
    clk = 1'b0;
    rst = 1'b0;
  	#60;
    rst = 1'b1;
end
  //initial begin
  //#200
  //  #finish();
  //end
endmodule