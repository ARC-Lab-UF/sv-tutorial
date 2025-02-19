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
    uvm_analysis_port #(axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH)) out_ap;

    // Adjusts prediction based on packet-level and single-beat transactions.
    bit is_packet_level;

    // Constructor
    function new(string name = "accum_predictor", uvm_component parent = null);
        super.new(name, parent);
        in_ae = new("in_ae", this); 
        in_fifo = new("in_fifo", this);
        out_ap = new("out_ap", this);  
        is_packet_level = 1'b0;
    endfunction

    function void connect_phase(uvm_phase phase);
        in_ae.connect(in_fifo.analysis_export);            
    endfunction

    virtual task run_phase(uvm_phase phase);        
        logic [accum_tb_pkg::OUTPUT_WIDTH-1:0] expected;
        axi4_stream_seq_item #(accum_tb_pkg::INPUT_WIDTH) in_item;
        axi4_stream_seq_item #(accum_tb_pkg::OUTPUT_WIDTH) out_item;
        
        in_item = new();
        expected = '0;

        if (is_packet_level) begin
            // In the case of packet-level transactions, compute expected over 
            // the entire packet, then send the result to the scoreboard.
            forever begin            
                in_fifo.get(in_item);                        
                assert(in_item.is_packet_level == is_packet_level);
                foreach (in_item.tdata[i]) expected += in_item.tdata[i];
    
                if (in_item.tlast) begin                                    
                    out_item = new();
                    out_item.is_packet_level = 1'b1;
                    out_item.tdata = expected;
                    out_ap.write(out_item);

                    // Clear expected for next packet.
                    expected = 0;
                end 
            end            
        end else begin
            // In the case of single-beat transactions, update expected and
            // send it to scoreboard, along with tlast status.             
            forever begin            
                in_fifo.get(in_item);       
                assert(in_item.is_packet_level == is_packet_level);                 
                expected += in_item.tdata;
                    
                out_item = new();
                out_item.is_packet_level = 1'b0;
                out_item.tdata = expected;
                out_item.tlast = in_item.tlast;
                out_ap.write(out_item);

                if (in_item.tlast) expected = 0;
            end            
        end
    endtask

endclass

`endif
