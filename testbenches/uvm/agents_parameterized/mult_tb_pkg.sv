package mult_tb_pkg;

    localparam int INPUT_WIDTH = 16;    

    import axi4_stream_pkg::*;

    `include "mult_sequence.svh"
    `include "mult_coverage.svh"
    `include "mult_scoreboard.svh"
    `include "mult_env.svh"
    `include "mult_base_test.svh"
    `include "mult_simple_test.svh"

endpackage