// Greg Stitt
// University of Florida

`ifndef _ACCUM_PREDICTOR_SVH_
`define _ACCUM_PREDICTOR_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import accum_tb_pkg::*;
`include "axi4_stream_seq_item.svh"

class accum_predictor extends uvm_component;
    `uvm_component_utils(accum_predictor)

    // Analysis export to receive inputs from the monitor.
    uvm_analysis_export #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH)) in_ae;
    uvm_tlm_analysis_fifo #(axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH)) in_fifo;

    // Analysis port to send expected outputs to the scoreboard.
    uvm_analysis_port #((axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH)) out_ap;

    // Constructor
    function new(string name = "accum_predictor", uvm_component parent = null);
        super.new(name, parent);
        in_ae = new("in_ae", this); 
        in_fifo = new("in_fifo", this);
        out_ap = new("out_ap", this);  
    endfunction

    function void connect_phase(uvm_phase phase);
        in_ae.connect(in_fifo.analysis_export);            
    endfunction

    virtual task run_phase(uvm_phase phase);        
        logic [accum_tb_pkg::OUTPUT_WIDTH-1:0] expected;
        axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH) in;
        axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH) out;
        
        in = new();        
        expected = '0;

        forever begin            
            in_fifo.get(in);                        
            expected += in.tdata;

            if (in.tlast) begin                
                expected = 0;
            end 
        end
    endtask

endclass

`endif
