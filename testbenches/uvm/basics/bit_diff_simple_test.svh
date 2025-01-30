// Greg Stitt
// University of Florida

// Here we have our first actual test. This particular test gets all of its
// functionality from the bit_diff_sequence. It simply creates and instance
// of that sequence, starts it via the sequencer, and then wait for the 
// sequencer to finish sending it to the driver.

`ifndef _BIT_DIFF_SIMPLE_TEST_SVH_
`define _BIT_DIFF_SIMPLE_TEST_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_base_test.svh"

class bit_diff_simple_test extends bit_diff_base_test;
    `uvm_component_utils(bit_diff_simple_test)

    function new(string name = "bit_diff_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        // We no longer need to build the environment because it is built by
        // the base test when we call this:
        super.build_phase(phase);        
    endfunction

    task run_phase(uvm_phase phase);
        bit_diff_sequence seq;

        // The objection mechanism in UVM is a way to coordinate and synchronize
        // the completion of phases. It's essentially a mechanism to prevent the
        // simulation from progressing to the next phase until all the components
        // that need to be finished in the current phase are done.
        //
        // Raising an objection here tells UVM that this component is has not 
        // finished with the current phase and that it is blocking the transition 
        // to the next phase.
        phase.raise_objection(this);

        // Our test creates a single sequence, which as we saw earlier 
        // sends num_tests bit_diff_items to the driver.
        seq = bit_diff_sequence::type_id::create("seq");        
        seq.start(env.agent.sequencer);
        
        // Dropping the objection allows the phase to end.
        phase.drop_objection(this);
    endtask

endclass

`endif
