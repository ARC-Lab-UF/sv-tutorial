`timescale 1 ns / 100 ps

module ram_sdp_tb #(
    parameter int NUM_TESTS = 10000,
    parameter int MIN_CYCLES_BETWEEN_TESTS = 1,
    parameter int MAX_CYCLES_BETWEEN_TESTS = 4,

    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 4,
    parameter bit REG_RD_DATA = 1'b1,
    parameter bit WRITE_FIRST = 1'b1,
    parameter string STYLE = "",
    parameter string ARCH = "quartus"
);
    logic                  clk=1'b0;
    logic                  rd_en;
    logic [ADDR_WIDTH-1:0] rd_addr;
    logic [DATA_WIDTH-1:0] rd_data;

    logic                  wr_en;
    logic [ADDR_WIDTH-1:0] wr_addr;
    logic [DATA_WIDTH-1:0] wr_data;

    ram_sdp #(
        .DATA_WIDTH (DATA_WIDTH),
        .ADDR_WIDTH (ADDR_WIDTH),
        .REG_RD_DATA(REG_RD_DATA),
        .WRITE_FIRST(WRITE_FIRST),
        .STYLE      (STYLE),
        .ARCH       (ARCH)
    ) DUT (
        .*
    );

    class memory_transaction;
        rand bit read_enable;
        rand bit [ADDR_WIDTH-1:0] read_addr;
        rand bit write_enable;
        rand bit [ADDR_WIDTH-1:0] write_addr;
        rand bit [DATA_WIDTH-1:0] write_data;
        rand bit use_same_address;
        rand int unsigned read_addr_index;

        // References to written addresses
        static bit [ADDR_WIDTH-1:0] written_addrs[$];
        static bit written_addr_exists[bit [ADDR_WIDTH-1:0]];

        constraint read_enable_c {
            written_addrs.size() == 0 -> (read_enable == 0);
            written_addrs.size() > 0 ->
            read_enable dist {
                1 :/ 50,
                0 :/ 50
            };
        }

        constraint write_enable_c {
            write_enable dist {
                1 :/ 50,
                0 :/ 50
            };
        }

        constraint addr_selection {
            use_same_address dist {
                1 :/ 5,
                0 :/ 95
            };

            if (use_same_address) {
                read_addr == write_addr;
            } else
            if (written_addrs.size() > 0) {
                read_addr_index < written_addrs.size();
                read_addr == written_addrs[read_addr_index];
            }
        }

        function void post_randomize();
            if (write_enable && !written_addr_exists.exists(write_addr)) begin
                written_addrs.push_back(write_addr);
                written_addr_exists[write_addr] = 1;
            end
        endfunction
    endclass


    bit addr_used[logic [ADDR_WIDTH-1:0]];

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end
    /*
    initial begin
        logic [ADDR_WIDTH-1:0] addr;

        for (int i = 0; i < NUM_TESTS; i++) begin
            addr = ADDR_WIDTH'($urandom);
            addr_used[addr] = 1'b1;
            wr_addr <= addr;
            wr_data <= DATA_WIDTH'($urandom);
            wr_en   <= 1'b1;
            @(posedge clk);
            wr_en <= 1'b0;
            repeat ($urandom_range(MIN_CYCLES_BETWEEN_TESTS, MAX_CYCLES_BETWEEN_TESTS - 1)) @(posedge clk);
        end
    end
*/

    initial begin
        automatic memory_transaction item = new;

        for (int i = 0; i < NUM_TESTS; i++) begin
            assert (item.randomize())
            else $fatal(1, "Randomization failed.");
            wr_en   <= item.write_enable;
            wr_addr <= item.write_addr;
            wr_data <= item.write_data;

            rd_en   <= item.read_enable;
            rd_addr <= item.read_addr;
            @(posedge clk);
            //repeat ($urandom_range(MIN_CYCLES_BETWEEN_TESTS, MAX_CYCLES_BETWEEN_TESTS - 1)) @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    logic [DATA_WIDTH-1:0] model[2**ADDR_WIDTH];
    logic [DATA_WIDTH-1:0] rd_data_ram, rd_data_model;
    logic rd_data_valid;

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

    assert property (@(posedge clk) rd_data_valid |-> rd_data === rd_data_model);
    assert property (@(posedge clk) !rd_en |=> $stable(rd_data));

endmodule
