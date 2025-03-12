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
    logic clk = 1'b0, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] data_in[8];
    logic [WIDTH-1:0] data_out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        data_in  <= '{default: '0};
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) data_in[j] <= $urandom;
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
    function automatic logic is_out_correct(logic [WIDTH-1:0] data_in[8]);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += data_in[i*2] * data_in[i*2+1];
        return sum == data_out;
    endfunction

    // Verify data_out and valid_out. 
    // Notice how this reads the latency from the DUT itself. Alternatively, it
    // is common to get the latency from package for the pipeline, or from a 
    // function in the package that calculates the latency based on various
    // parameters.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> is_out_correct($past(data_in, DUT.LATENCY, en)));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(data_out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> data_out == '0);

endmodule


// Module: simple_pipeline_with_en_tb1.
// Description: This testbench corrects the bug from the previous module.

module simple_pipeline_with_en_tb1 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    logic clk = 1'b0, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] data_in[8];
    logic [WIDTH-1:0] data_out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        data_in  <= '{default: '0};
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) data_in[j] <= $urandom;
            valid_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    // In this version, all values we need to compare are provided as inputs from
    // the sampled values in the assertion.
    function automatic logic is_out_correct(logic [WIDTH-1:0] data_in[8], logic [WIDTH-1:0] data_out);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += data_in[i*2] * data_in[i*2+1];
        return sum == data_out;
    endfunction

    // Verify data_out and valid_out.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> is_out_correct($past(data_in, DUT.LATENCY, en), data_out));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(data_out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> data_out == '0);

endmodule


// Module: simple_pipeline_with_en_tb2.
// Description: This testbench provides a simpler modeling strategy that works
// well when the pipeline has a single output.

module simple_pipeline_with_en_tb2 #(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    logic clk = 1'b0, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] data_in[8];
    logic [WIDTH-1:0] data_out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock        
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        data_in  <= '{default: '0};
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) data_in[j] <= $urandom;
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
    function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] data_in[8]);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += data_in[i*2] * data_in[i*2+1];
        return sum;
    endfunction

    // Verify data_out and valid_out.
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> data_out == model($past(data_in, DUT.LATENCY, en)));
    assert property (@(posedge clk) disable iff (rst) en [-> DUT.LATENCY] |=> valid_out == $past(valid_in, DUT.LATENCY, en));

    // Verify the reset clears the outputs until the pipeline has filled.
    assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> DUT.LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> DUT.LATENCY]);

    // Verify enable stalls the outputs.
    assert property (@(posedge clk) !en |=> $stable(data_out) && $stable(valid_out));

    // Make sure all pipeline stages are reset.
    assert property (@(posedge clk) rst |=> data_out == '0);

endmodule


// Next, we'll use a package with a latency function to all the latency of the
// pipeline to be read from anywhere. In this case, the latency is constant,
// but in many cases the latency will be a function of the modules' configuration
// parameters, which should be added as parameters to the latency function.
package simple_pipeline_with_en_pkg;
    function automatic int latency();
        return 4;
    endfunction
endpackage


// Module: simple_pipeline_with_en_tb3.
// Description: This testbench uses a package (instead of hierarchical access)
// to get the latency, and demonstrates several other assertion strategy for
// exceptions from a typical pipeline. It also demonstrates how to use local
// variables in properties.

module simple_pipeline_with_en_tb3 
    import simple_pipeline_with_en_pkg::latency;
#(
    parameter int NUM_TESTS = 10000,
    parameter int WIDTH = 8
);
    // Get the latency from the package for the DUT module.
    localparam int LATENCY = simple_pipeline_with_en_pkg::latency();

    logic clk = 1'b0, rst, en, valid_in, valid_out;
    logic [WIDTH-1:0] data_in[8];
    logic [WIDTH-1:0] data_out;

    simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

    initial begin : generate_clock        
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Reset the circuit.
        rst      <= 1'b1;
        en       <= 1'b0;
        valid_in <= 1'b0;
        data_in  <= '{default: '0};
        repeat (5) @(posedge clk);
        @(negedge clk);
        rst <= 1'b0;
        @(posedge clk);

        // Run the tests.      
        for (int i = 0; i < NUM_TESTS; i++) begin
            en <= $urandom;
            for (int j = 0; j < 8; j++) data_in[j] <= $urandom;
            valid_in <= $urandom;
            @(posedge clk);
        end

        $display("Tests completed.");
        disable generate_clock;
    end

    function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] data_in[8]);
        logic [WIDTH-1:0] sum = 0;
        for (int i = 0; i < 4; i++) sum += data_in[i*2] * data_in[i*2+1];
        return sum;
    endfunction

    // One potential issue with waiting for LATENCY occurrences of en and then 
    // verifying the output is that it validates tests where valid_in can be 0 
    // or 1. If that's what you want, then the previous approach is fine. 
    // However, in some cases, you might have undefined inputs when 
    // valid_in == 0, which might cause exceptions to the model. For example, if
    // the module reads from a memory using an address that doesn't contain 
    // valid data, which is likely when valid_in == 0, data_out might be 'X.
    //
    // To avoid those exceptions, we can explicitly wait for a valid_in, and 
    // then validate the output after LATENCY occurrences of en. This strategy
    // is shown below:
    assert property (@(posedge clk) disable iff (rst) valid_in && en |-> en [-> LATENCY] ##1 data_out == model($past(data_in, LATENCY, en)));

    // Up to this point, our assertion strategy has been to validate the output
    // by looking back through time to get the input at the start of the
    // corresponding test. In some situations, it is easier to save the input at
    // the start of the test in a local variable, and then refer to that local
    // variable once the output becomes available. To declare a local variable
    // we need to declare the property separately from the assertion:
    property check_output_p;
        logic [WIDTH-1:0] correct_data_out;
        // The antecedent of the implication waits for valid_in && en, and then 
        // saves the correct output into correct_data_out by computing the model
        // based on the current input at the start of the test. You can have
        // other statements execute in the antecedent by having addition commas
        // within the parantheses.
        @(posedge clk) disable iff (rst) (valid_in && en, correct_data_out = model(data_in)) |-> en [-> LATENCY] ##1 data_out == correct_data_out;
    endproperty
    assert property (check_output_p);

    // The following property looks very similar to the previous one, but has a 
    // subtle error. It starts a test everytime valid_in is asserted, regardless
    // of whether or not en is asserted. If en is 0, correct_data_out is computed
    // from an invalid input. The simple fix is to wait for valid_in && en.
    //
    // You might be confused now because none of the earlier assertion used en
    // in the trigger condition. Those earlier assertions worked because if en
    // was 0 when valid_in was 1, the test starts and waits for LATENCY
    // enables, but then gets the corresponding input by looking into the past
    // LATENCY cycles when en was asserted. So, the previous assertions always
    // used the appropriate input for the model regardless of when the trigger
    // condition became true.
    /*property bad_p;
        logic [WIDTH-1:0] correct_data_out;        
        @(posedge clk) disable iff (rst) (valid_in, correct_data_out = model(data_in)) |-> en [-> LATENCY] ##1 data_out == correct_data_out;
    endproperty
    assert property (bad_p);*/

    // We'll still verify valid_out the previous way since we want to test
    // situations where valid_in is 0 and 1.
    assert property (@(posedge clk) disable iff (rst) en [-> LATENCY] |=> valid_out == $past(valid_in, LATENCY, en));

    // Same as before.
    assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> LATENCY]);
    assert property (@(posedge clk) $fell(rst) |-> !valid_out throughout en [-> LATENCY]);
    assert property (@(posedge clk) !en |=> $stable(data_out) && $stable(valid_out));    
    assert property (@(posedge clk) rst |=> data_out == '0);

endmodule
