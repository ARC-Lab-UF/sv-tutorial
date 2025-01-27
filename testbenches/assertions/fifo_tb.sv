// Greg Stitt
// University of Florida
// This file contains several testbenches for the fifo module that illustrate
// different strategies that can simplify a testbench.

// Module: fifo_tb1
// Description: This testbench illustrates assertions for signals inside the
// DUT. This is an incomplete testbench and is only used to demonstrate
// hierarchical access.

module fifo_tb1 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
);
    logic             clk;
    logic             rst;
    logic             full;
    logic             wr_en;
    logic [WIDTH-1:0] wr_data;
    logic             empty;
    logic             rd_en;
    logic [WIDTH-1:0] rd_data;

    fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        rst     <= 1'b1;
        rd_en   <= 1'b0;
        wr_en   <= 1'b0;
        wr_data <= '0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            wr_data <= $urandom;
            wr_en   <= $urandom;
            rd_en   <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests Completed.");
    end

    always @(posedge clk) begin

        // To check certain FIFO properties, we need to see inside of the
        // FIFO module. We could do that by adding debugging signals to the port,
        // but that is cumbersome. Instead, SystemVerilog lets us see inside
        // entities anywhere within the hierarchy by using the instance name
        // followed by a peiod. So, DUT. gives us access to any signal from
        // inside the FIFO instance we are testing. This sometimes referred to
        // "whitebox" testing.
        //
        // Here, we check to make sure that there is never a write while the FIFO
        // is full, or a read while the FIFO is empty.
        assert (!(DUT.valid_wr && full));
        assert (!(DUT.valid_rd && empty));
    end

    // These are all equivalent assertions without the always block.
    assert property (@(posedge clk) !(DUT.valid_wr && full));
    assert property (@(posedge clk) !(DUT.valid_rd && empty));
    assert property (@(posedge clk) DUT.valid_wr |-> !full);
    assert property (@(posedge clk) DUT.valid_rd |-> !empty);

endmodule


// Module: fifo_tb2_bad
// Description: This testbench adds an assertion that verifies that the read 
// data is correct. There is are several problems here that we will fix in the 
// next testbench.

module fifo_tb2_bad #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
);
    logic             clk;
    logic             rst;
    logic             full;
    logic             wr_en;
    logic [WIDTH-1:0] wr_data;
    logic             empty;
    logic             rd_en;
    logic [WIDTH-1:0] rd_data;

    fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        rst     <= 1'b1;
        rd_en   <= 1'b0;
        wr_en   <= 1'b0;
        wr_data <= '0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            wr_data <= $urandom;
            wr_en   <= $urandom;
            rd_en   <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests Completed.");
    end

    assert property (@(posedge clk) DUT.valid_wr |-> !full);
    assert property (@(posedge clk) DUT.valid_rd |-> !empty);

    // We still need to verify the read data output from the FIFO, which we do
    // here with a custom property.
    property check_output;
        // Declare local data that will have a new instance for every test.
        logic [WIDTH-1:0] data;

        // Create a property where if there is a valid write, we save the wr_data
        // into the local data variable. The valid write then implies that at
        // some indefinite point in the future (i.e. ##[1:$]) there will be a
        // valid read from the FIFO that has matching data. Note that we aren't
        // using the DUT.valid_wr signal because since that signal is inside the
        // DUT, it might not be correct.
        //
        // One bug here is that a single instance of a valid read could
        // successfully terminate multiple assertions for writes that had the
        // same write data. This means that some of the valid reads will be left
        // unchecked. TODO: Verify this with an example.
        //
        // Another bug is that when using ##[1:$], if there is never a situation
        // where the subsequent condition is true, then no error will be reported
        // because no assertion will ever be terminated. So, this basically will
        // only ever report successul tests unless we restrict the time range.
        // For example, if we change the range to ##[1:2] we will start to see
        // errors if they exist. However, that would also require reads to occur
        // within two cycles, or errors would be falsely reported.
        @(posedge clk) (wr_en && !full,
        data = wr_data
        ) |-> ##[1:$] rd_en && !empty ##1 rd_data == data;
    endproperty  // check_output

    assert property (check_output) begin
        // If we want to print a custom message when a property passes an
        // assertion test, we can do that here. However, it is very important
        // to realize that access to signals provides the postponed (i.e. the
        // updated) value compared to the signals used in the property. This can
        // be very confusing, so to make sure the same values are reported, you
        // can use the $sampled version of each signal, which provides the prior
        // value. See the following for details:
        //
        // https://www.accellera.org/images/resources/videos/SystemVerilog_Assertions_Tutorial_2016.pdf
        //$info("PASSED [%0t] rd_data=%h", $realtime, $sampled(rd_data));
    end

    // An else can be provided for the assertion failure if the default
    // assertion message is not sufficient.

endmodule  // fifo_tb2


// Module: fifo_tb3
// Description: This testbench fixes the issue with the prior testbench by
// ensuring every read is matched with a write. This is a good strategy for
// any FIFO-like behavior.

module fifo_tb3 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
);
    logic             clk;
    logic             rst;
    logic             full;
    logic             wr_en;
    logic [WIDTH-1:0] wr_data;
    logic             empty;
    logic             rd_en;
    logic [WIDTH-1:0] rd_data;

    fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        rst     <= 1'b1;
        rd_en   <= 1'b0;
        wr_en   <= 1'b0;
        wr_data <= '0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            wr_data <= $urandom;
            wr_en   <= $urandom;
            rd_en   <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests Completed.");
    end

    assert property (@(posedge clk) DUT.valid_wr |-> !full);
    assert property (@(posedge clk) DUT.valid_rd |-> !empty);

    // To solve the problem with the previous testbench, we assign each write
    // a unique tag, and then maintain a "serving" counter so we can determine
    // which read applies to which write.
    //
    // The following two functions are called from within the custom property
    // to update the state of the simulation.
    int tag = 0, serving = 0;
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
       // Local variables to save the tag and data for a write.
       int wr_tag;
       logic [WIDTH-1:0] data;
      
       // On each valid write, we save the current tag into a local variable, 
       // update the global tag counter, and save the write data.
       // The write implies that at some point in the future there will be a
       // valid read with a wr_tag that matches the current serving ID. We only
       // care about the first matching instance, so we use the first_match
       // function.
       //
       // Finally, when there is a valid read with the matching tag, on the
       // next cycle (i.e. ##1) the read data should match the original write
       // data.
       @(posedge clk) (wr_en && !full, wr_tag=tag, inc_tag(), data=wr_data) |-> first_match(##[1:$] (rd_en && !empty && serving==wr_tag, inc_serving())) ##1 rd_data==data;
    endproperty
            
    ap_check_output : assert property (check_output);
        
endmodule


// Module: fifo_tb4
// Description: 
// While the previous testbench works well and is concise, it runs the risk of
// many people not understanding it. Not many people are experts in properties
// and sequences, so it runs of the risk of being difficult to maintain.
//
// When you become too uncomfortable with the complexity of an assertion, it is
// time to consider alternatives.
//
// This testbench uses a queue as a reference model for the FIFO, which eliminates
// the complexity of the previous assertion. Since a queue is a FIFO, it is 
// natural choice for modeling the FIFO.

module fifo_tb4 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
);
    logic             clk;
    logic             rst;
    logic             full;
    logic             wr_en;
    logic [WIDTH-1:0] wr_data;
    logic             empty;
    logic             rd_en;
    logic [WIDTH-1:0] rd_data;

    fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        rst     <= 1'b1;
        rd_en   <= 1'b0;
        wr_en   <= 1'b0;
        wr_data <= '0;
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;

        for (int i = 0; i < NUM_TESTS; i++) begin
            wr_data <= $urandom;
            wr_en   <= $urandom;
            rd_en   <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests Completed.");
    end

    assert property (@(posedge clk) DUT.valid_wr |-> !full);
    assert property (@(posedge clk) DUT.valid_rd |-> !empty);

    logic [WIDTH-1:0] correct_rd_data;
    logic [WIDTH-1:0] model_queue[$];

    // Model the functionality of the FIFO with a queue.
    always_ff @(posedge clk or posedge rst)
        if (rst) begin
            model_queue = {};
        end else begin
            // IMPORTANT: We need to get the size before any modifications
            // since that's how the FIFO works.
            automatic int size = model_queue.size();

            // Pop the front element on a valid read.
            if (rd_en && size > 0) begin            
               correct_rd_data <= model_queue.pop_front();

                // Or, alternatively:
                //model_queue = model_queue[1:$];
            end

            // Push the write data on a valid write.
            if (wr_en && size < DEPTH) begin            
                model_queue.push_back(wr_data);

                // Or, alternatively:
                //model_queue = {model_queue, wr_data};
            end
        end

    assert property (@(posedge clk) rd_en && model_queue.size() > 0 |=> rd_data == correct_rd_data);

endmodule

