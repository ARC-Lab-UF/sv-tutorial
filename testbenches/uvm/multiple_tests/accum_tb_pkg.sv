// Used to specify the parameter configuration for the DUT.

package accum_tb_pkg;

    localparam int INPUT_WIDTH = 16;
    localparam int OUTPUT_WIDTH = 32;

    import axi4_stream_pkg::*;

    `include "accum_sequence.svh"
    `include "accum_coverage.svh"
    `include "accum_scoreboard.svh"
    `include "accum_env.svh"
    `include "accum_base_test.svh"
    `include "accum_single_beat_test.svh"
    `include "accum_packet_test.svh"

endpackage
