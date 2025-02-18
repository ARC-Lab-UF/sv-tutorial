// Greg Stitt
// University of Florida

`ifndef _ACCUM_SIMPLE_TEST_SVH_
`define _ACCUM_SIMPLE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;

`include "accum_sequence.svh"
`include "accum_base_test.svh"

class accum_simple_test extends accum_base_test;
    `uvm_component_utils(accum_simple_test)

    function new(string name = "accum_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        accum_sequence seq;
        phase.raise_objection(this);

        seq = accum_sequence::type_id::create("seq");        
        seq.start(env.agent_in.sequencer);

        phase.drop_objection(this);
    endtask

endclass

`endif
