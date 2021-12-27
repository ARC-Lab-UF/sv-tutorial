module fifo_tb1;

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
      rst = 1'b1;
      rd_en = 1'b0;
      wr_en = 1'b0;
      wr_data = '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      rst = 1'b0;

      for (int i=0; i < 1000; i++) begin
	 wr_data = $random;
	 wr_en = $random;
	 rd_en = $random;
	 @(posedge clk);	 
      end

      disable generate_clock;      
   end
   
   always @(posedge clk) begin

      // To check certain FIFO properties, we need to see inside of the
      // FIFO module. We could do that by adding debugging signals to the port,
      // but that is cumbersome. Instead, SystemVerilog lets us see inside
      // entities anywhere within the hierarchy by using the instance name
      // followed by a peiod. So, DUT. gives us access to any signal from
      // inside the FIFO instance we are testing.
      //
      // Here, we check to make sure that there is never a write while the FIFO
      // is full, or a read while the FIFO is empty.  
      assert(!(DUT.valid_wr && full));
      assert(!(DUT.valid_rd && empty));      
   end // always @ (posedge clk)

   assert property (@(posedge clk) !(DUT.valid_wr && full));
   assert property (@(posedge clk) !(DUT.valid_rd && empty));
   
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);
   
endmodule

module fifo_tb2;

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

      for (int i=0; i < 1000; i++) begin
	 wr_data = $random;
	 wr_en = $random;
	 rd_en = $random;
	 @(posedge clk);	 
      end

      disable generate_clock;      
   end
   
   always @(posedge clk) begin

      // To check certain FIFO properties, we need to see inside of the
      // FIFO module. We could do that by adding debugging signals to the port,
      // but that is cumbersome. Instead, SystemVerilog lets us see inside
      // entities anywhere within the hierarchy by using the instance name
      // followed by a peiod. So, DUT. gives us access to any signal from
      // inside the FIFO instance we are testing.
      //
      // Here, we check to make sure that there is never a write while the FIFO
      // is full, or a read while the FIFO is empty.  
      assert(!(DUT.valid_wr && full));
      assert(!(DUT.valid_rd && empty));      
   end // always @ (posedge clk)

   assert property (@(posedge clk) !(DUT.valid_wr && full));
   assert property (@(posedge clk) !(DUT.valid_rd && empty));
   
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   property check_output;
      logic [WIDTH-1:0] data;
      // https://verificationacademy.com/forums/systemverilog/printing-value-local-variable-within-property
      
      //@(posedge clk) (DUT.valid_wr, data=wr_data, $display("Starting wr_en at %0t with data=%h", $time, wr_data)) |-> ##[1:100] DUT.valid_rd |-> (rd_data == data, $display("Valid read at time %0t with rd_data=%h, data=%h", $time, rd_data, data));
      // I don't like this because there could be valid reads with incorrect
      // data as long as the correct data eventually shows up on a valid read
      @(posedge clk) (DUT.valid_wr, data=wr_data, $display("Starting wr_en at %0t with data=%h", $time, wr_data)) |-> ##[1:100] (DUT.valid_rd && rd_data == data, $display("Valid read at time %0t with rd_data=%h, data=%h", $time, rd_data, data));
   endproperty // check_output
   
   assert property (check_output) begin
      // Messages get postponed values. Must use $sampled to get previous value.
      // https://www.accellera.org/images/resources/videos/SystemVerilog_Assertions_Tutorial_2016.pdf
      $display("PASSED (%0t): rd_en=%b, rd_data=%h", $time, $sampled(DUT.valid_rd), $sampled(rd_data));      
   end   
/* -----\/----- EXCLUDED -----\/-----
   else begin
      $display("FAILED: rd_en=%b, rd_data=%h", DUT.valid_rd, rd_data);      
   end;   
 -----/\----- EXCLUDED -----/\----- */
   
endmodule // fifo_tb2


module fifo_tb3;

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

      for (int i=0; i < 1000; i++) begin
	 wr_data = $random;
	 wr_en = $random;
	 rd_en = $random;
	 @(posedge clk);	 
      end

      disable generate_clock;      
   end
      
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   property check_output;
      logic [WIDTH-1:0] data;
      @(posedge clk) (DUT.valid_wr, data=wr_data, $display("Starting wr_en at %0t with data=%h", $time, wr_data)) |-> ##[1:$] (DUT.valid_rd, $display("(Time %0t) valid_rd=%b", $time, DUT.valid_rd)) |-> (rd_data == data, $display("(Time %0t) rd_data=%h, data=%h", $time, rd_data, data));
   endproperty // check_output
   
   assert property (check_output) begin
      // Messages get postponed values. Must use $sampled to get previous value.
      // https://www.accellera.org/images/resources/videos/SystemVerilog_Assertions_Tutorial_2016.pdf
      $display("PASSED (%0t): rd_en=%b, rd_data=%h", $time, $sampled(DUT.valid_rd), $sampled(rd_data));      
   end   
   else begin
      $display("FAILED (%0t): rd_en=%b, rd_data=%h", $time, $sampled(DUT.valid_rd), $sampled(rd_data));      
   end;   
   
endmodule


module fifo_tb4;

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

      for (int i=0; i < 1000; i++) begin
	 wr_data = $random;
	 wr_en = $random;
	 rd_en = $random;
	 @(posedge clk);	 
      end

      disable generate_clock;      
   end
      
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   property check_output;
      logic [WIDTH-1:0] data;

      // https://verificationacademy.com/forums/systemverilog/nested-implication
      
      @(posedge clk) first_match((DUT.valid_wr, data=wr_data) ##[1:$] DUT.valid_rd) |-> rd_data == data;
      
      //@(posedge clk) (DUT.valid_wr, data=wr_data, $display("Starting wr_en at %0t with data=%h", $time, wr_data)) |-> first_match(##[1:$] (DUT.valid_rd, $display("(Time %0t) valid_rd=%b", $time, DUT.valid_rd)) |-> (rd_data == data, $display("(Time %0t) rd_data=%h, data=%h", $time, rd_data, data));
   endproperty // check_output
   
   assert property (check_output) begin
      // Messages get postponed values. Must use $sampled to get previous value.
      // https://www.accellera.org/images/resources/videos/SystemVerilog_Assertions_Tutorial_2016.pdf
      $display("PASSED (%0t): rd_en=%b, rd_data=%h", $time, $sampled(DUT.valid_rd), $sampled(rd_data));      
   end   
   else begin
      $display("FAILED (%0t): rd_en=%b, rd_data=%h", $time, $sampled(DUT.valid_rd), $sampled(rd_data));      
   end;   
   
endmodule


module fifo_tb5;

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
   
   // Credit to Ben Cohen for this solution:
   // https://verificationacademy.com/forums/systemverilog/checking-order-fifo-component
   // Explanation here: http://systemverilog.us/vf/Uniqueness_v2.pdf
   property check_output;      
      int wr_tag;
      logic [WIDTH-1:0] data;
      
      @(posedge clk) (DUT.valid_wr, wr_tag=tag, inc_tag(), data=wr_data) |-> first_match(##[1:$] (DUT.valid_rd && serving==wr_tag, inc_serving())) ##0 rd_data==data;
   endproperty
            
   ap_check_output : assert property (check_output);

   c_full_writes : cover property (@(posedge clk) wr_en && full);
   
      
endmodule
