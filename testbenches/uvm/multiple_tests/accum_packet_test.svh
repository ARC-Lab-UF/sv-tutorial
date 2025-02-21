// Greg Stitt
// University of Florida

// This class tests the DUT with packet-level transactions.

`ifndef _ACCUM_PACKET_TEST_SVH_
`define _ACCUM_PACKET_TEST_SVH_

class accum_packet_test extends accum_base_test;
    `uvm_component_utils(accum_packet_test)

    function new(string name = "accum_packet_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        accum_packet_sequence seq;
        phase.raise_objection(this);

        seq = accum_packet_sequence::type_id::create("seq");        
        seq.start(env.agent_in.sequencer);

        phase.drop_objection(this);
    endtask

endclass

`endif
