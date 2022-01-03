// Greg Stitt
// University of Florida
//
// This file illustrates a basic example of constrained-random verification 
// (CRV), where we use classes with random variables and constraints to 
// generate tests.

`timescale 1 ns / 10 ps

// Class: add_item
// Description: this class represents the basic "transaction object" used by the
// the testbench. In general, a "transaction" model is intended to separate the
// details of the communication from the details of the implementation. This
// concept is not obvious from this simple example, but for more complex 
// examples, we'll see transactions being more abstract than the 
// implementations they are used to test.
//
// For more complex testbenches, transaction objects get transferred between 
// multiple classes, all with different purposes. For this simple example, the
// transaction object simply encapsulates all the involved signals, while 
// specifying constraints to control the distribution of inputs used in testing.
//
// For now, you can think of a transaction object as an abstraction of the
// structure of the each input used for testing.

class add_item #(int width);

   // Use rand to enable randomization of inputs. We'll see later how to 
   // actually create the random values.
   // Note that bit is similar to logic, but only with 0 and 1 values, which is
   // all we care about in the testbench.
   rand bit [width-1:0] in0;
   rand bit [width-1:0] in1;

   // Randc ensures that all possible values are used before repeating.
   randc bit carry_in;

   // It doesn't hurt to make these rand, but we don't have to since they
   // correspond to outputs from the DUT.
   bit [width-1:0] sum;
   bit carry_out;

   constraint c_in0_dist { in0 dist{0 :/ 10, 2**width-1 :/ 10, [1:2**width-2] :/ 80}; }
   constraint c_in1_dist { in1 dist{0 :/ 10, 2**width-1 :/ 10, [1:2**width-2] :/ 80}; }
   
   function void print(); 
      $display("Add Item (Time=%0t): in0=%d, in1=%d, carry_in=%b, sum=%d, carry_out=%b", $time, in0, in1, carry_in, sum, carry_out);      
   endfunction
endclass

// Module: add_tb
// Description: A testbench that uses CRV with an appropriate distribution 
// to eliminate all the manual tests that were specified in the same testbench
// in the coverage tutorials.

module add_tb;

   localparam WIDTH = 16;
   localparam NUM_TESTS = 10000;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic 	     carry_out, carry_in;
   
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic 	     clk;

   // Here we reuse the same covergroup from the coverage tutorial.
   covergroup cg @(posedge clk);
      cin : coverpoint carry_in {bins one = {1}; option.at_least = 100;}
      cout : coverpoint carry_out {bins one = {1}; option.at_least = 10;}

      in0_extremes : coverpoint in0 {
	 bins zero = {0};
	 bins max_ = {{WIDTH{1'b1}}};
	 option.at_least = 10; 
      }
      in1_extremes : coverpoint in0 {
	 bins zero = {0};
	 bins max_ = {{WIDTH{1'b1}}};
	 option.at_least = 10; 
      }

      in0_full : coverpoint in0 {option.auto_bin_max = 16;}
      in1_full : coverpoint in1 {option.auto_bin_max = 16;}
      in0_cross_in1 : cross in0_full, in1_full;

      in0_in1_eq_0 : coverpoint (in0==0 && in1==0) {bins true = {1'b1};}
      in0_in1_eq_max : coverpoint (in0=={WIDTH{1'b1}} && in1=={WIDTH{1'b1}}) {bins true = {1'b1};}  
   endgroup
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   add_item #(.width(WIDTH)) item;
   cg cg_inst;      
   initial begin      
      item = new;
      cg_inst = new;      
      $timeformat(-9, 0, " ns");

      // With the add item class that uses CRV, we no longer need to specify
      // manual tests. We simply just generate a number of tests using the
      // randomize function, which creates the input distribution we requested.
      // That distribution is sufficient for achieving 100% coverage without
      // any manual tests.
      for (int i=0; i < NUM_TESTS; i++) begin
	 
	 // Assigns random value to all the rand variables in the add item.
	 item.randomize();

	 // Assigns the random inputs to the DUT inputs.
	 in0 = item.in0;
	 in1 = item.in1;
	 carry_in = item.carry_in;

	 // Uncomment to print out the values of the add item.
	 // Note that the outputs are always 0 because they are declared
	 // as rand, and we are connecting them to the DUT outputs.
	 // For this example, they could be deleted.
	 //item.print();	 
	 @(posedge clk);
      end

      $display("Tests completed.");
      disable generate_clock;      
   end

   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);
   
endmodule // add_tb


