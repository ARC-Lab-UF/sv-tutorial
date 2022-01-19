// Greg Stitt
// University of Florida

// Module: mult_tb
// Description: Testbench for the different mult modules in mult.sv.

module mult_tb;

   localparam INPUT_WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [INPUT_WIDTH-1:0] in0, in1;
   logic [INPUT_WIDTH*2-1:0] product_signed, product_unsigned;

   // TODO: Change comments to test different modules.
   // Apparently SV doesn't allow the .* operator for parameters, only ports.
   //mult1 #(.IS_SIGNED(1'b1), .INPUT_WIDTH(INPUT_WIDTH)) DUT_SIGNED (.product(product_signed), .*);
   //mult1 #(.IS_SIGNED(1'b0), .INPUT_WIDTH(INPUT_WIDTH)) DUT_UNSIGNED (.product(product_unsigned), .*);
   mult2 #(.IS_SIGNED(1'b1), .INPUT_WIDTH(INPUT_WIDTH)) DUT_SIGNED (.product(product_signed), .*);
   mult2 #(.IS_SIGNED(1'b0), .INPUT_WIDTH(INPUT_WIDTH)) DUT_UNSIGNED (.product(product_unsigned), .*);

   initial begin

      logic [INPUT_WIDTH*2-1:0] correct_product_signed, correct_product_unsigned;
          
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 correct_product_signed = signed'(in0) * signed'(in1);
	 correct_product_unsigned = in0 * in1;	 
	 #10;
	 if (product_signed != correct_product_signed)
	    $display("ERROR (time %0t): signed product = %d instead of %d.", $realtime, product_signed, correct_product_signed);

	 if (product_unsigned != correct_product_unsigned)
	    $display("ERROR (time %0t): unsigned product = %d instead of %d.", $realtime, product_unsigned, correct_product_unsigned);    		 
      end
   end      
endmodule // mult_tb


// Module: mult_high_low_tb
// Description: Testbench for the different mult_high_low modules in mult.sv.

module mult_high_low_tb;

   localparam INPUT_WIDTH = 16;
   localparam NUM_TESTS = 1000;
   
   logic [INPUT_WIDTH-1:0] in0, in1;
   logic [INPUT_WIDTH-1:0] high_signed, low_signed;
   logic [INPUT_WIDTH-1:0] high_unsigned, low_unsigned;

   // TODO: Change comments to test different modules.
   // Apparently SV doesn't allow the .* operator for parameters, only ports.
   mult_high_low1 #(.IS_SIGNED(1'b1), .INPUT_WIDTH(INPUT_WIDTH)) DUT_SIGNED (.high(high_signed), .low(low_signed), .*);
   mult_high_low1 #(.IS_SIGNED(1'b0), .INPUT_WIDTH(INPUT_WIDTH)) DUT_UNSIGNED (.high(high_unsigned), .low(low_unsigned), .*);
   //mult_high_low2 #(.IS_SIGNED(1'b1), .INPUT_WIDTH(INPUT_WIDTH)) DUT_SIGNED (.high(high_signed), .low(low_signed), .*);
   //mult_high_low2 #(.IS_SIGNED(1'b0), .INPUT_WIDTH(INPUT_WIDTH)) DUT_UNSIGNED (.high(high_unsigned), .low(low_unsigned), .*);

   initial begin

      logic [INPUT_WIDTH*2-1:0] product_signed, product_unsigned, correct_product_signed, correct_product_unsigned;
          
      for (int i=0; i < NUM_TESTS; i++) begin
	 in0 = $random;
	 in1 = $random;
	 correct_product_signed = signed'(in0) * signed'(in1);
	 correct_product_unsigned = in0 * in1;	 
	 #10;
	 product_signed = {high_signed, low_signed};
	 product_unsigned = {high_unsigned, low_unsigned};	 
	 if (product_signed != correct_product_signed)
	    $display("ERROR (time %0t): signed product = %d instead of %d.", $realtime, product_signed, correct_product_signed);

	 if (product_unsigned != correct_product_unsigned)
	    $display("ERROR (time %0t): unsigned product = %d instead of %d.", $realtime, product_unsigned, correct_product_unsigned);    		 
      end
   end  
endmodule // mult_high_low_tb

