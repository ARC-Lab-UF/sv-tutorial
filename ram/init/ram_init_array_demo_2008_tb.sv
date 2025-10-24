// Greg Stitt
// StittHub (www.stitt-hub.com)

// For post-synth sims, change POST_SYNTH_SIM to 1

`timescale 1 ns / 100 ps

module ram_init_array_demo_2008_tb
    import ram_init_demo_pkg::RAM_INIT_DEMO_ARRAY;
#(
    parameter int NUM_TESTS = 10000,

    parameter int DATA_WIDTH = 8,
    parameter int ADDR_WIDTH = 6,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "",

    parameter bit POST_SYNTH_SIM = 1'b0
);
    logic                  clk=1'b0;
    logic                  rd_en;
    logic [ADDR_WIDTH-1:0] rd_addr;
    logic [DATA_WIDTH-1:0] rd_data;

    logic                  wr_en;
    logic [ADDR_WIDTH-1:0] wr_addr;
    logic [DATA_WIDTH-1:0] wr_data;

    if (POST_SYNTH_SIM) begin : l_post_synth
        ram_init_array_demo_2008 DUT (
            .clk    (clk),
            .rd_en  (rd_en),
            .rd_addr(rd_addr),
            .rd_data(rd_data),
            .wr_en  (wr_en),
            .wr_addr(wr_addr),
            .wr_data(wr_data)
        );
    end else begin : l_functional
        ram_init_array_demo_2008 #(
            .DATA_WIDTH (DATA_WIDTH),
            .ADDR_WIDTH (ADDR_WIDTH),
            .REG_RD_DATA(REG_RD_DATA),
            .WRITE_FIRST(WRITE_FIRST),
            .STYLE      (STYLE)
        ) DUT (
            .clk    (clk),
            .rd_en  (rd_en),
            .rd_addr(rd_addr),
            .rd_data(rd_data),
            .wr_en  (wr_en),
            .wr_addr(wr_addr),
            .wr_data(wr_data)
        );
    end

    bit addr_used[logic [ADDR_WIDTH-1:0]];
    logic [ADDR_WIDTH-1:0] used_addresses[$];

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

    initial begin
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] wr_data_temp;
        logic wr_en_temp;

        $timeformat(-9, 0, " ns");

        wr_en   <= 1'b0;
        wr_addr <= '0;
        wr_data <= '0;
        rd_en   <= 1'b0;
        rd_addr <= '0;

        // Allow time for post-synth initialization.
        repeat (20) @(posedge clk);

        $display("[%0t] Testing init values.", $realtime);

        // Test init values.
        for (int i = 0; i < 2 ** ADDR_WIDTH; i++) begin
            wr_en   <= 1'b0;
            wr_addr <= '0;
            rd_en   <= 1'b1;
            rd_addr <= i;
            @(posedge clk);
        end

        $display("[%0t] Testing general RAM behavior.", $realtime);

        // General tests.
        for (int i = 0; i < NUM_TESTS; i++) begin
            assert (std::randomize(wr_data_temp))
            else $fatal(1, "Randomization failed.");

            addr = $urandom;
            wr_en_temp = $urandom;
            wr_en   <= wr_en_temp;
            wr_addr <= addr;
            wr_data <= wr_data_temp;

            if (wr_en_temp && !addr_used.exists(addr)) begin
                used_addresses.push_back(addr);
            end

            rd_en   <= used_addresses.size() == 0 ? 1'b0 : $urandom;
            rd_addr <= used_addresses.size() == 0 ? '0 : used_addresses[$urandom_range(0, used_addresses.size()-1)];
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    logic [DATA_WIDTH-1:0] model[2**ADDR_WIDTH] = ram_init_demo_pkg::RAM_INIT_DEMO_ARRAY;
    logic [DATA_WIDTH-1:0] rd_data_ram, rd_data_model;
    logic rd_data_valid = 1'b0;

    initial begin
        forever begin
            @(posedge clk);
            if (wr_en) model[wr_addr] <= wr_data;
            if (rd_en) begin
                if (WRITE_FIRST && wr_en && rd_addr == wr_addr) rd_data_ram <= wr_data;
                else rd_data_ram <= model[rd_addr];
            end
        end
    end

    if (!REG_RD_DATA) begin : no_reg_rd_data
        assign rd_data_model = rd_data_ram;
        always_ff @(posedge clk) rd_data_valid <= rd_en;
    end else begin : reg_rd_data
        logic rd_data_valid_delay = 1'b0;
        always_ff @(posedge clk) begin
            if (rd_en) begin
                rd_data_model <= rd_data_ram;
                rd_data_valid_delay <= rd_en;
                rd_data_valid <= rd_data_valid_delay;
            end
        end
    end

    assert property (@(posedge clk) rd_data_valid |-> rd_data === rd_data_model)
    else $error("rd_data = %0h vs rd_data_model = %0h", $sampled(rd_data), $sampled(rd_data_model));
    assert property (@(posedge clk) !rd_en |=> $stable(rd_data));
    cover property (@(posedge clk) wr_en && rd_en && wr_addr == rd_addr);
endmodule
