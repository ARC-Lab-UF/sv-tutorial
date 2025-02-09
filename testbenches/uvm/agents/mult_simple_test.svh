// Greg Stitt
// University of Florida

// A simple test for the multiplier that generates two sequences and sends them
// to the DUT in parallel by using a fork.

`ifndef _MULT_SIMPLE_TEST_SVH_
`define _MULT_SIMPLE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_tb_pkg::*;

`include "mult_sequence.svh"
`include "mult_base_test.svh"

class mult_simple_test extends mult_base_test;
    `uvm_component_utils(mult_simple_test)

    function new(string name = "mult_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        mult_sequence seq_in0, seq_in1;
        
        phase.raise_objection(this);

        // Since the DUT uses separate interfaces for each input, we'll want
        // separate sequence instances for each.
        seq_in0 = mult_sequence::type_id::create("seq_in0");
        seq_in1 = mult_sequence::type_id::create("seq_in1");

        // IMPORTANT: start() blocks until the sequence has finished, so we
        // can't call these sequentially otherwise we'll send all the test
        // values to one input without sending anything to the other. By
        // forking, each call to start() runs in parallel, so the sequences
        // arrive at the DUT at the same time.
        //
        // Note that as synchronization of multiple sequences becomes more 
        // complex, you might want to consider a virtual sequence, which is
        // intended to handle complex situations involving synchronization of
        // multiple sequences, including different types of sequences.
        fork
            seq_in0.start(env.agent_in0.sequencer);
            seq_in1.start(env.agent_in1.sequencer);
        join

        phase.drop_objection(this);
    endtask

endclass

`endif
