// Greg Stitt
// University of Florida
//
// This file illustrates how to create a testbench for a simple pipeline
// with an enable. Notice how concise the testbench is. More importantly,
// notice how to make it work most pipelines, you only need to change the
// model. I personally use this as a template for pipeline testbenches in
// the vast majority of my pipelines.

`timescale 1 ns / 100 ps

// Module: simple_pipeline_with_en_tb_bad.
// Description: This testbench demonstrates a concise way of testing all the
// functionality of a pipeline, but with a subtle bug that is common.

module simple_pipeline_with_en_tb_bad #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    logic clk, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] in[8];
    logic [WIDTH-1:0] out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        in       <= '{default: '0};
        for (int i = 0; i < 5; i++) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) in[j] <= $urandom;
            valid_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // Although this function is a correct reference model for the pipeline,
    // when it is used as part of the assertion, it provides incorrect
    // results because the out variable has already been updated with the new
    // output value, but the in input corresponds to the old sampled value provided
    // by the assertion.
    //
    // IMPORTANT: avoid reading from variables that aren't provided as parameters
    // from the assertion itself. Assertions sample values on clock edges, whereas
    // other variable can be updated at any time.
    function automatic logic is_out_correct(logic [WIDTH-1:0] in[8]);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += in[i*2] * in[i*2+1];
        return sum == out;
    endfunction

    // Verify data_out and valid_out.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> out == is_out_correct($past(in, DUT.LATENCY, en)));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> out == '0);

endmodule


// Module: simple_pipeline_with_en_tb1.
// Description: This testbench corrects the bug from the previous module.

module simple_pipeline_with_en_tb1 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    logic clk, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] in[8];
    logic [WIDTH-1:0] out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        in       <= '{default: '0};
        for (int i = 0; i < 5; i++) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) in[j] <= $urandom;
            valid_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // In this version, all values we need to compare are provided as inputs from
    // the sampled values in the assertion.
    function automatic logic is_out_correct(logic [WIDTH-1:0] in[8], logic [WIDTH-1:0] out);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += in[i*2] * in[i*2+1];
        return sum == out;
    endfunction

    // Verify data_out and valid_out.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> is_out_correct($past(in, DUT.LATENCY, en), out));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> out == '0);

endmodule


// Module: simple_pipeline_with_en_tb2.
// Description: This testbench provides a simpler modeling strategy that works
// well when the pipeline has a single output.

module simple_pipeline_with_en_tb2 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    logic clk, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] in[8];
    logic [WIDTH-1:0] out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        in       <= '{default: '0};
        for (int i = 0; i < 5; i++) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) in[j] <= $urandom;
            valid_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // In this example, we use a simpler function that returns the correct
    // output, instead of comparing with the correct output directly. When
    // there is a single output, this strategy is preferred, but when the
    // output is an array, you often need a function to verify all output values.
    function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] in[8]);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += in[i*2] * in[i*2+1];
        return sum;
    endfunction

    // Verify data_out and valid_out.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> out == model($past(in, DUT.LATENCY, en)));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> out == '0);

endmodule
