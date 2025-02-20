// Greg Stitt
// University of Florida

// This class tests the accumulator using transactions consisting of single
// beats, as opposed to entire packets.

`ifndef _ACCUM_SINGLE_BEAT_TEST_SVH_
`define _ACCUM_SINGLE_BEAT_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;

`include "accum_sequence.svh"
`include "accum_base_test.svh"

class accum_single_beat_test extends accum_base_test;
    `uvm_component_utils(accum_single_beat_test)

    function new(string name = "accum_single_beat_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        accum_beat_sequence seq;
        phase.raise_objection(this);

        seq = accum_beat_sequence::type_id::create("seq");        
        seq.start(env.agent_in.sequencer);

        phase.drop_objection(this);
    endtask

endclass

`endif
