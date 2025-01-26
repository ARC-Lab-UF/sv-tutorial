// Greg Stitt, Wesley Piard, Nashmin Alam
// University of Florida

// This file illustrates several ways of writing testbenches for a delay
// entity. The first approach should be avoided and is included to show how
// much simpler a testbench can be that effectively uses assertions and
// implication.

`timescale 1 ns / 100 ps

// Module: delay_tb1
// Description: Testbench for the delay entity. This is a more complicated
// testbench that creates a model of the delay by preserving the correct 
// outputs in an array. 
//
// While this testbench works, the model is overly complicated, and we can
// replace a lot of the code with more concise assertions and other constructs
// which are shown in the later modules.

module delay_tb1 #(
    parameter int NUM_TESTS = 1000,
    parameter int CYCLES = 4,
    parameter int WIDTH = 8
);
    logic             clk = 1'b0;
    logic             rst;
    logic             en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    delay #(
        .CYCLES(CYCLES),
        .WIDTH (WIDTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst <= 1'b1;
        en <= 1'b0;
        data_in <= '0;
        repeat (5) @(posedge clk);

        @(negedge clk);
        rst <= 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            data_in <= $urandom;
            en <= $urandom;
            @(posedge clk);
        end

        // Stop the always blocks.
        disable generate_clock;
        disable check_output;
        $display("Tests completed.");
    end

    // In the code below, we create our delay model and verify the DUT.

    // Round up the buffer to the next power of 2, which is necessary because
    // of the addressing logic.
    localparam int BUFFER_SIZE = 2 ** $clog2(CYCLES);

    // Reset the buffer contents.
    logic [WIDTH-1:0] buffer[BUFFER_SIZE] = '{default: '0};

    // Addresses for accessing the buffer. The inputs are written to the buffer
    // and the outputs are read from the buffer.
    logic [$clog2(CYCLES)-1:0] wr_addr = 0;
    logic [$clog2(CYCLES)-1:0] rd_addr;

    logic [WIDTH-1:0] correct_out;
    // The read address should be offset from the write address by CYCLES + 1.
    assign rd_addr = wr_addr - CYCLES + 1;

    // Verify the outputs by comparing the actual output with the model's output.
    initial begin : check_output
        forever begin
            @(posedge clk);
            if (data_out != correct_out) $error("[%0t] out = %0h instead of %0h.", $realtime, data_out, correct_out);
        end
    end

    // Note that instead of the check_output initial block, we could have just
    // done this:
    assert property (@(posedge clk) disable iff (rst) data_out == correct_out);

    // Create the reference model.
    generate
        if (CYCLES == 0) begin
            assign correct_out = data_in;
        end else begin
            // Imitate a memory with a one-cycle read delay to store the 
            // correct outputs.
            always @(posedge clk, posedge rst) begin
                if (rst) correct_out <= '0;
                else if (en) begin
                    buffer[wr_addr] = data_in;
                    correct_out <= buffer[rd_addr];
                    wr_addr <= wr_addr + 1'b1;
                end
            end
        end
    endgenerate
endmodule  // delay_tb1


// Module: delay_tb2
// Description: In this testbench, we demonstrate the use of a queue to provide
// a much simpler reference model than the previous testbench.

module delay_tb2 #(
    parameter int NUM_TESTS = 1000,
    parameter int CYCLES = 4,
    parameter int WIDTH = 8
);
    logic             clk = 1'b0;
    logic             rst;
    logic             en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    delay #(
        .CYCLES(CYCLES),
        .WIDTH (WIDTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst     <= 1'b1;
        en      <= 1'b0;
        data_in <= '0;
        repeat (5) @(posedge clk);

        @(negedge clk);
        rst <= 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            data_in <= $urandom;
            en      <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // In this testbench, we model the delay using a queue. A queue is declared
    // in a way that is similar to an unpacked array, but uses $ for the range.
    logic [WIDTH-1:0] model_queue[$];

    always_ff @(posedge clk or posedge rst)
        if (rst) begin
            // On reset, initialize the queue with CYCLES 0 values to mimic
            // the reset behavior of the delay.
            model_queue = {};
            for (int i = 0; i < CYCLES; i++) model_queue.push_back('0);

            // Or, alternatively:
            //for (int i=0; i < CYCLES; i++) model_queue = {model_queue, WIDTH'(0)};
        end else if (en) begin
            // Update the queue by popping the front and pushing the new input.
            // Note that these are blocking assignments.
            // 
            // The void cast is not necessary, but if we call a function that returns
            // a value and don't assign to anything, the simulator will report a
            // warning. The void cast makes it explicit we don't want the return
            // value.
            void'(model_queue.pop_front());
            model_queue.push_back(data_in);

            // Or, alternatively:
            //model_queue = {model_queue[1:$], in};
        end

    // The output should simply always be the front of the reference queue.
    // IMPORTANT: In previous examples, we saw race conditions being caused by
    // one process writing with blocking assignments, and another process reading
    // those values. There is no race condition here because an assert
    // always samples the "preponed" values of the referenced signals. In other
    // words, you can think of the sampled values as the ones before the
    // simulator updates anything on a clock edge. Alternatively, you can think
    // of the values as the ones just before the posedge of the clock.
    // Interestingly, this means that any reference to the clock here will always
    // be 0, because the clock is always 0 right before a rising clock edge.
    assert property (@(posedge clk) data_out == model_queue[0]);

endmodule  // delay_tb2


// Module: delay_tb3
// Description: This testbench replaces the complex functionality of the
// original testbench with assertions and implication. This testbench hardcodes
// the enable to 1, which we will extend later.

module delay_tb3 #(
    parameter int NUM_TESTS = 1000,
    parameter int CYCLES = 4,
    parameter int WIDTH = 8
);
    logic             clk = 1'b0;
    logic             rst;
    logic             en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    delay #(
        .CYCLES(CYCLES),
        .WIDTH (WIDTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst     <= 1'b1;
        en      <= 1'b1;
        data_in <= '0;
        repeat (5) @(posedge clk);

        @(negedge clk);
        rst <= 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            data_in <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // Incorrect attempt 1:
    // Although this correctly checks to see if the output matches the input
    // from CYCLES previous cycles, it ignores the value of reset, which could
    // cause failures while reset is asserted.
    //
    //assert property(@(posedge clk) data_out == $past(data_in, CYCLES));

    // Incorrect attempt 2:
    // This assertion disables checks during reset. However, despite working for
    // small CYCLES values, it only works conicidentally because the testbench
    // uses an input that matches the reset value for the output. As soon as
    // the CYCLES exceeds the number of cycles for reset, this starts failing.
    //
    //assert property(@(posedge clk) disable iff (rst) data_out == $past(data_in, CYCLES));

    // Ultimately, what we need is to check the output in two states:
    // 1) When all the outputs are based on the reset, and
    // 2) When the output actually corresponds to a delayed input.
    //
    // To determine what state we are in, we'll add a counter that simply counts
    // until reaching CYCLES. When count < CYCLES, we know that an input hasn't
    // reached the output yet. When count == CYCLES, we can safely use $past.
    int count;
    always_ff @(posedge clk or posedge rst)
        if (rst) count <= 0;
        else if (count < CYCLES) count <= count + 1;

    // Don't check for the output matching the delayed input until an input
    // has reached the output.
    assert property (@(posedge clk) disable iff (rst || count < CYCLES) data_out == $past(data_in, CYCLES));

    // Check for correct outputs during reset and until inputs reach the output.
    assert property (@(posedge clk) disable iff (count == CYCLES) data_out == '0);

endmodule  // delay_tb3


// Module: delay_tb4
// Description: This testbench improves upon the previous one by including the
// enable signal.

module delay_tb4 #(
    parameter int NUM_TESTS = 1000,
    parameter int CYCLES = 4,
    parameter int WIDTH = 8
);
    logic             clk = 1'b0;
    logic             rst;
    logic             en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    delay #(
        .CYCLES(CYCLES),
        .WIDTH (WIDTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst     <= 1'b1;
        en      <= 1'b0;
        data_in <= '0;
        repeat (5) @(posedge clk);

        @(negedge clk);
        rst <= 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            data_in <= $urandom;
            en      <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    int count;
    always_ff @(posedge clk or posedge rst)
        if (rst) count <= 0;
        else if (en && count < CYCLES) count <= count + 1;

    // Here, we simply add a gating parameter to the $past signal using the
    // en signal. This causes $past to ignore values in cycles when en
    // is 0.
    assert property (@(posedge clk) disable iff (rst) count == CYCLES |-> data_out == $past(data_in, CYCLES, en));

    // Although conceptually identical to the above assertion, this assertion
    // fails in the first cycle that count == CYCLES. This problem is identical to
    // what we saw in the register example, where the disable appears to 
    // use values that get updated after the clock edge, where the other
    // variables are sampled on the clock edge.
    // TODO: Read the SV standard for the exact definition of disable.
    //assert property (@(posedge clk) disable iff (rst || count < CYCLES) data_out == $past(data_in, CYCLES, en));

    assert property (@(posedge clk) disable iff (rst) count < CYCLES |-> data_out == '0);

    // Check to make sure the output doesn't change when not enabled
    assert property (@(posedge clk) disable iff (rst) !en |=> $stable(data_out));

endmodule  // delay_tb4


// Module: delay_tb5
// Description: This testbench improves upon the previous one by eliminating the
// need for using a counter to determine when to enable various assertions.

module delay_tb5 #(
    parameter int NUM_TESTS = 1000,
    parameter int CYCLES = 4,
    parameter int WIDTH = 8
);
    logic             clk = 1'b0;
    logic             rst;
    logic             en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    delay #(
        .CYCLES(CYCLES),
        .WIDTH (WIDTH)
    ) DUT (
        .*
    );

    initial begin : generate_clock
        forever #5 clk <= ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        // Initialize the circuit.
        rst     <= 1'b1;
        en      <= 1'b0;
        data_in <= '0;
        repeat (5) @(posedge clk);

        @(negedge clk);
        rst <= 1'b0;

        // Genereate NUM_TESTS random tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            data_in <= $urandom;
            en      <= $urandom;
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    // en[->CYCLES] replaces the previous counter by doing the same thing in 
    // much less code. This operator is called the "go to" repetition operator. 
    // It causes the antecedent to trigger after en has been asserted in CYCLES 
    // cycles, which do not have to be consecutive.
    assert property (@(posedge clk) disable iff (rst) en [-> CYCLES] |=> data_out == $past(data_in, CYCLES, en));

    // To verify the reset, we can check to make sure that data_out is 0
    // throughout the entire window of time between when reset is cleared
    // until en has been asserted CYCLES times. The following assertion
    // accomplishes this very concisely.
    //
    // Thanks to Nashmin Alam and Wesley Piard for helping discover this.
    assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> CYCLES]);

    // Verify the output during a reset.
    assert property (@(posedge clk) rst |=> data_out == '0);

    // Check to make sure the output doesn't change when not enabled.
    assert property (@(posedge clk) disable iff (rst) !en |=> $stable(data_out));

    // COMMON MISTAKES:
    // The following assertion is similar to the one we used above. However, it
    // does not use implication based on the misunderstanding that en[->CYCLES]
    // will stop after CYCLES assertions of en. While each instance of 
    // en[->CYCLES] stops at that time, the assertion generates a window for
    // *every* possible window of CYCLES enables during the entire sim. So, 
    // this assertion will fail after the first test because data_out will
    // clearly not be 0 at later points in the simulation. The above version
    // worked because it was only triggeer once when rst fell.
    //
    //assert property (@(posedge clk) disable iff (rst) data_out == '0 throughout en [-> CYCLES]);

    // The following is another potential solution that has a common misunderstanding.
    // When reading this in English, it sounds like what we want: wait until 
    // reset falls, that check that data_out is 0 until we've seen CYCLES enables.
    // However, that isn't what this actually means. It means wait until reset
    // falls, then verify that data_out is 0 **until the beginning** of a window
    // of time between 0 and CYCLES enables. Because that window starts immediately,
    // this assertion actually doesn't check anything. This is dangerous because
    // it always succeeds even when our DUT is wrong. Test this for yourself by
    // setting the reset value of the delay to a non-zero value. This assertion
    // will still succeed.
    //
    //assert property (@(posedge clk) disable iff (rst) $fell(rst) |-> data_out == '0 until en [-> CYCLES]);

    // DEBUGGING TIPS
    // One challenge with complex assertions is that you have to also verify the
    // assertion itself. While failures are reported automatically, sometimes
    // it is useful to analyze when an assertion succeeds. You can do this as
    // follows. The behavior is likely simulator specific, but in Questa, I get the
    // following for CYCLES=4:
    //  ** Info: [85 ns] Assertion Succeeded for data_out = 0
    // #    Time: 85 ns Started: 55 ns  Scope: ....
    //
    // Notice the "Time" of 85 ns (when the assertion finished) and the 
    // "Started" (when the assertion was triggered. The corresponds to exactly
    // the first clock after reset, and the clock after CYCLES enables.
    // This tells me it is checking the exact range of time I wanted.
    //
    //assert property (@(posedge clk) $fell(rst) |-> data_out == '0 throughout en [-> CYCLES]) begin
    //    $info("[%0t] Assertion Succeeded for data_out = %0h", $realtime, $sampled(data_out));
    //end

    // Similarly, on an assertion failure, it can help to print the variables 
    // used in the assertion. This can be done by adding and "else" to the 
    // assertion. Make sure to use $sampled when printing and variables,
    // otherwise you will see updated values that often cause confusion.
    // You can also print with $past().
    //
    //assert property (@(posedge clk) disable iff (rst) data_out == '0 throughout en [-> CYCLES])
    //else $error("[%0t]: actual data_out = %0d, expected 0", $realtime, $sampled(data_out));

endmodule  // delay_tb5
