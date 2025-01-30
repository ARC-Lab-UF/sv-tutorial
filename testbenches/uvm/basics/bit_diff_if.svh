// Greg Stitt
// University of Florida

// Interface for the bit_diff module. This has been cleanedup up from the
// previous testbench examples do demonstrate what are generally considered
// good practices. Also, I've removed the BFM name from earlier examples, even
// though the interface does provide monitoring and driving tasks normally
// associated with BFMs. I did this because the UVM agent will take over the 
// BFM responsibilties (with assistance from the interface methods). 

`ifndef _BIT_DIFF_IF_
`define _BIT_DIFF_IF_

import bit_diff_if_pkg::*;

interface bit_diff_if #(
    // Providing the default width based off a package in order to simplify
    // use of a parameterized interface withing UVM. This can be convenient, but
    // only works when the UVM testbench needs all instances of the interface use
    // the same width. If different widths are needed for different instances, 
    // we'll need to expand the testbench, as shown in later examples.
    parameter int WIDTH = bit_diff_if_pkg::WIDTH
) (
    input logic clk
);
    logic rst, go, done;
    logic [WIDTH-1:0] data;
    logic signed [$clog2(2*WIDTH+1)-1:0] result;

    task automatic reset(int cycles);
        rst <= 1'b1;
        go  <= 1'b0;
        repeat (cycles) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);
    endtask

    // Start the DUT with the specified data by creating a 1-cycle pulse on go.
    task automatic start(input logic [WIDTH-1:0] data_);
        data <= data_;
        go   <= 1'b1;
        @(posedge clk);
        go <= 1'b0;
    endtask

    // Detect when an execution has completed.
    task automatic wait_for_done();
        @(posedge clk iff (!done));
        @(posedge clk iff (done));
    endtask

    // Detect when the DUT starts executing. This task internally tracks the 
    // active status of the DUT and returns every time it becomes active.
    task automatic wait_for_start();
        static logic is_active = 1'b0;

        forever begin
            @(posedge clk);
            if (rst) is_active = 1'b0;
            else begin
                if (done) is_active = 1'b0;
                if (!is_active && go) begin
                    is_active = 1'b1;
                    break;
                end
            end
        end
    endtask

endinterface

`endif
