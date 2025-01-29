// Greg Stitt
// University of Florida

// Module: fifo_tb
// Description: This testbench extends the FIFO testbench from the assertions
// example with basic cover properties.

module fifo_tb #(
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
        if (rst) model_queue = {};
        else begin
            automatic int size = model_queue.size();
            if (rd_en && size > 0) correct_rd_data <= model_queue.pop_front();
            if (wr_en && size < DEPTH) model_queue.push_back(wr_data);
        end

    assert property (@(posedge clk) rd_en && model_queue.size() > 0 |=> rd_data == correct_rd_data);

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

    // NOTE: My formatter is putting the labels on different lines. I don't 
    // recommend that.
    cp_write :
    cover property (@(posedge clk) wr_en);
    cp_read :
    cover property (@(posedge clk) rd_en);

    // We should also check to make sure we test the FIFO for writes when the
    // FIFO is full, and reads when the FIFO is empty. Although either of these
    // would usually be an error by the user of the FIFO, we want to make sure
    // that incorrect usage does not corrupt the internal state of the FIFO.
    cp_write_while_full :
    cover property (@(posedge clk) wr_en && full);
    cp_read_while_empty :
    cover property (@(posedge clk) rd_en && empty);

    // To see the coverage results, you often have to enable it in your specific
    // simulator. For Questa, you can start it with vsim -coverage. You also
    // might have to right click the files you want to include for coverage and
    // select properties. There is then a coverage tab, with different options
    // you can enable.   

endmodule

