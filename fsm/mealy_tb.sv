// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: mealy_tb
// Description: A testbench for the mealy module. This testbench only checks
// that done is asserted. It mainly provides an input stimulus and should not
// be considered a thorough test.

module mealy_tb;

   logic clk=0, rst, go, ack, done, en;

   mealy DUT (.*);

   initial begin : generate_clock
      while (1)
	#5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, " ns");
      
      // Reset the FSM.
      rst = 1'b1;
      ack = 1'b0;
      go = 1'b0;      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;
      @(posedge clk);

      // Start the FSM.
      go = 1'b1;
      for (int i=0; i < 5; i++)
	@(posedge clk);
      
      ack = 1'b1;
      @(posedge clk);
      ack = 1'b0;      
      if (!done)
	$display("ERROR (time %0t): done not asserted.", $realtime);	
      
      // Clear go
      go = 1'b0;
      @(posedge clk);

      // Repeat the execution to test the RESTART state
      go = 1'b1;
      for (int i=0; i < 5; i++)
	@(posedge clk);
      
      ack = 1'b1;
      @(posedge clk);
      ack = 1'b0;      
      if (!done)
	$display("ERROR (time %0t): done not asserted after restart.", $realtime);	      
      go = 1'b0;

      disable generate_clock;      
   end
   
endmodule
