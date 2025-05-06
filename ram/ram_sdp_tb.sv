// Greg Stitt
// StittHub (www.stitt-hub.com)

`timescale 1 ns / 100 ps

module ram_sdp_tb #(
    parameter int NUM_TESTS = 10000,

    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 8,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "",
    parameter string ARCH = "vivado"
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
        .clk    (clk),
        .rd_en  (rd_en),
        .rd_addr(rd_addr),
        .rd_data(rd_data),
        .wr_en  (wr_en),
        .wr_addr(wr_addr),
        .wr_data(wr_data)
    );

    bit addr_used[logic [ADDR_WIDTH-1:0]];
    logic [ADDR_WIDTH-1:0] used_addresses[$];

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

    initial begin
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] wr_data_temp;
        logic wr_en_temp;

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

            rd_en   <= $urandom;
            rd_addr <= used_addresses[$urandom_range(0, used_addresses.size()-1)];
            @(posedge clk);
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    logic [DATA_WIDTH-1:0] model[2**ADDR_WIDTH];
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

    assert property (@(posedge clk) rd_data_valid |-> rd_data === rd_data_model);
    assert property (@(posedge clk) !rd_en |=> $stable(rd_data));
    cover property (@(posedge clk) wr_en && rd_en && wr_addr == rd_addr);
endmodule


// This testbench performs very similar tests as the previous testbench, but
// does so using randomization constraints. The takeaway point is that that 
// constrained randomization, while flexible, can be very slow due to all the
// constraint solving. Don't overuse it or your simulation times will suffer.

module ram_sdp_tb_slow #(
    parameter int NUM_TESTS = 10000,

    parameter int DATA_WIDTH = 16,
    parameter int ADDR_WIDTH = 8,
    parameter bit REG_RD_DATA = 1'b0,
    parameter bit WRITE_FIRST = 1'b0,
    parameter string STYLE = "",
    parameter string ARCH = "vivado"
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
        .clk    (clk),
        .rd_en  (rd_en),
        .rd_addr(rd_addr),
        .rd_data(rd_data),
        .wr_en  (wr_en),
        .wr_addr(wr_addr),
        .wr_data(wr_data)
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

        // This replicates the behavior of the previous testbench. It is more
        // flexible, but also much slower due to all the constraint solving.
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

    initial begin : generate_clock
        forever #5 clk <= !clk;
    end

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
        end

        disable generate_clock;
        $display("Tests completed.");
    end

    logic [DATA_WIDTH-1:0] model[2**ADDR_WIDTH];
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

    assert property (@(posedge clk) rd_data_valid |-> rd_data === rd_data_model);
    assert property (@(posedge clk) !rd_en |=> $stable(rd_data));
    cover property (@(posedge clk) wr_en && rd_en && wr_addr == rd_addr);
endmodule
