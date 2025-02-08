// Greg Stitt
// University of Florida

`ifndef _MULT_SIMPLE_TEST_SVH_
`define _MULT_SIMPLE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

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
        //mult_sequence seq;
        phase.raise_objection(this);

        //seq = mult_sequence::type_id::create("seq");        
        //seq.start(env.agent.sequencer);
        
        phase.drop_objection(this);
    endtask

endclass

`endif
