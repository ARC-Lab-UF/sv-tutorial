// Greg Stitt
// University of Florida
// This file contains several testbenches for the fifo module that illustrate
// different assertion strategies that can simplify a testbench.

// Module: fifo_tb4
// Description: This testbench extends the testbenches from the assertions
// examples with cover properties.

module fifo_tb;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic 	     clk;
   logic 	     rst;
   logic 	     full;
   logic 	     wr_en;
   logic [WIDTH-1:0] wr_data;
   logic 	     empty; 
   logic 	     rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");
      rst = 1'b1;
      rd_en = 1'b0;
      wr_en = 1'b0;
      wr_data = '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;

      for (int i=0; i < 10000; i++) begin
	 wr_data = $random;
	 wr_en = $random;
	 rd_en = $random;
	 @(posedge clk);	 
      end

      disable generate_clock;
      $display("Tests Completed.");
   end
      
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   int tag=0, serving=0;   
   function void inc_tag();
      tag = tag + 1'b1;
   endfunction
   
   function void inc_serving();
      serving = serving + 1'b1; 
   endfunction
   
   property check_output;
      int wr_tag;
      logic [WIDTH-1:0] data;
      @(posedge clk) (DUT.valid_wr, wr_tag=tag, inc_tag(), data=wr_data) |-> first_match(##[1:$] (DUT.valid_rd && serving==wr_tag, inc_serving())) ##0 rd_data==data;
   endproperty
            
   ap_check_output : assert property (check_output);

   // At a bare minimum, we want to make sure that the testbench actually tests
   // a write and a read. This is virtually guaranteed based on the number of
   // tests performed above, but this is how we actually verify it.
   //
   // To ensure a specific test happens (i.e., is "covered"), we can use cover
   // properties. Cover properties work similarly to assertion
   // properties, except the simulator only tracks the number of times that
   // the property passes. Basically, simulators ignore when assertions pass
   // and when covers fail.
   //
   // So, in these cases, the simulator would tell us the number of writes and
   // reads that were performed. If that number is > 0, we have at least covered
   // these basic tests.
   cp_write : cover property (@(posedge clk) wr_en);
   cp_read : cover property (@(posedge clk) rd_en);

   // We should also check to make sure we test the FIFO for writes when the
   // FIFO is full, and reads when the FIFO is empty. Although either of these
   // would usually be an error by the user of the FIFO, we want to make sure
   // that incorrect usage does not corrupt the internal state of the FIFO.
   cp_write_while_full : cover property (@(posedge clk) wr_en && full);
   cp_read_while_empty : cover property (@(posedge clk) rd_en && empty);

   // To see the coverage results, you often have to enable it in your specific
   // simulator. For Modelsim, you can start it with vsim -coverage. You also
   // have to right click the files you want to include for coverage and
   // select properties. There is then a coverage tab, with different options
   // you can enable.   
endmodule
