// Greg Stitt
// University of Florida

`timescale 1 ns / 100 ps

// Module: delay_tb
// Description: Testbench for the delay entity. This is a more complicated
// testbench that preserves the correct outputs in an array.

module delay_tb1;

   localparam NUM_TESTS = 1000;
      
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic 	     clk = 1'b0;
   logic 	     rst;
   logic 	     en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
	   .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
	   .RESET_VALUE(RESET_VALUE))
   DUT (.*);
   
   initial begin : generate_clock
      while (1)
	#5 clk = ~clk;      
   end

   // Round up the buffer to the next power of 2, which is necessary because
   // of the addressing logic.
   localparam BUFFER_SIZE = 2**$clog2(CYCLES);

   // Reset the buffer contents to the reset value.
   logic [WIDTH-1:0] buffer[BUFFER_SIZE] = '{default: RESET_VALUE};

   // Addresses for accessing the buffer. The inputs are written to the buffer
   // and the outputs are read from the buffer.
   logic [$clog2(CYCLES)-1:0] wr_addr = 0;
   logic [$clog2(CYCLES)-1:0] rd_addr;
           
   initial begin
      $timeformat(-9, 0, " ns");

      // Initialize the circuit.
      rst = 1'b1;
      en = 1'b0;
      in = '0;      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      // Genereate NUM_TESTS random tests.
      for (int i=0; i < NUM_TESTS; i++) begin
	 in = $random;
	 en = $random;

	 // If the delay is enabled, write the new input to it and update
	 // the write address.
	 if (en) begin
	    @(posedge clk);	    
	    wr_addr ++;	    
	 end
	 else	   
	   @(posedge clk);
      end  

      // Stop the always blocks.
      disable generate_clock;
      disable check_output;
      $display("Tests completed.");      
   end

   logic [WIDTH-1:0] correct_out;
   // The read address should be offset from the write address by CYCLES + 1.
   assign rd_addr = wr_addr - CYCLES + 1;
         
   initial begin : check_output
      while (1) begin
	 @(posedge clk);
	 
	 // Check outputs on the falling edge to give time for values to change.
	 @(negedge clk);
	 if (out != correct_out)
	   $display("ERROR (time %0t): out = %h instead of %h.", $realtime, out, correct_out);   
      end
   end

   generate
      if (CYCLES == 0) begin
	 assign correct_out = in;	 
      end
      else begin      
	 // Imitate a memory with a one-cycle read delay to store the 
	 // correct outputs.
	 always @(posedge clk, posedge rst) begin
	    if (rst)
	      correct_out <= RESET_VALUE;           
	    else if (en) begin 
	       buffer[wr_addr] = in;
	       correct_out <= buffer[rd_addr];
	    end
	 end
      end
   endgenerate
endmodule // delay_tb


module delay_tb2;

   localparam NUM_TESTS = 1000;
      
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic 	     clk = 1'b0;
   logic 	     rst;
   logic 	     en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
	   .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
	   .RESET_VALUE(RESET_VALUE))

   // For this testbench, hardcode enable to 1 to illustrate assertion property
   DUT (.en(1'b1), .*);
   
   initial begin : generate_clock
      while (1)
	#5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, " ns");

      // Initialize the circuit.
      rst = 1'b1;
      in = '0;      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      // Genereate NUM_TESTS random tests.
      for (int i=0; i < NUM_TESTS; i++) begin
	 in = $random;
	 @(posedge clk);
      end  

      // Stop the always blocks.
      disable generate_clock;
      $display("Tests completed.");      
   end

   // Incorrect attempt 1:
   // Although this correctly checks to see if the output matches the input
   // from CYCLES previous cycles, it ignores the value of reset, which could
   // cause failures while rest is asserted.
   //
   //assert property(@(posedge clk) out == $past(in, CYCLES));

   // Incorrect attempt 2:
   // This assertion disables checks during reset. However, despite working for
   // small CYCLES values, it only works conicidentally because the testbench
   // uses an input that matches the reset value for the output. As soon as
   // the CYCLES exceeds the number of cycles for reset, this starts failing.
   //
   //assert property(@(posedge clk) disable iff (rst) out == $past(in, CYCLES));

   // Ultimately, what we need is to check the output in two states:
   // 1) When all the outputs are based on the reset, and
   // 2) When the output actually corresponds to a delayed input.
   //
   // To determine what state we are in, we'll add a counter that simply counts
   // until reaching CYCLES. When count < CYCLES, we know that an input hasn't
   // reached the output yet. When count == CYCLES, we can safely use $past
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < CYCLES) count ++;

   // Don't check for the output matching the delayed input until enough cycles
   // have passed.
   assert property(@(posedge clk) disable iff (rst || count < CYCLES) out == $past(in, CYCLES));

   // Check for correct outputs during reset and until inputs reach the output.
   assert property(@(posedge clk) disable iff (count == CYCLES) out == RESET_VALUE);
   
endmodule // delay_tb2


module delay_tb3;

   localparam NUM_TESTS = 1000;
      
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic 	     clk = 1'b0;
   logic 	     rst;
   logic 	     en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
	   .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
	   .RESET_VALUE(RESET_VALUE))
   
   // For this testbench, hardcode enable to 1 to illustrate assertion property
   DUT (.*);
   
   initial begin : generate_clock
      while (1)
	#5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, " ns");

      // Initialize the circuit.
      rst = 1'b1;
      en = 1'b0;      
      in = '0;      
      for (int i=0; i < 5; i++)
	@(posedge clk);

      rst = 1'b0;

      // Genereate NUM_TESTS random tests.
      for (int i=0; i < NUM_TESTS; i++) begin
	 in = $random;
	 en = $random;	 
	 @(posedge clk);
      end  

      // Stop the always blocks.
      disable generate_clock;
      $display("Tests completed.");      
   end

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < CYCLES) count ++;

   // Here, we simply add a gating parameter to the $past signal using the
   // enable signal.
   //assert property(@(posedge clk) disable iff (rst) (count < CYCLES || out == $past(in, CYCLES, en), $display ("Time (%0t): out=%h, past=%h", $time, out, $past(in, CYCLES, en))));
   assert property(@(posedge clk) disable iff (rst) count < CYCLES || out == $past(in, CYCLES, en));

   // TODO: for some reason, this fails once in Modelsim in the first cycle 
   // where count == CYCLES
   //   assert property(@(posedge clk) disable iff (rst || count < CYCLES) (out == $past(in, CYCLES, en), $display ("Time (%0t): out=%h, past=%h", $time, out, $past(in, CYCLES, en))));

   assert property(@(posedge clk) disable iff (rst) count == CYCLES || out == RESET_VALUE);

   // Check to make sure the output doesn't change when not enabled
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));
         
endmodule // delay_tb3

