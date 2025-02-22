// Greg Stitt
// University of Florida

`ifndef _BIT_DIFF_MONITOR_SVH_
`define _BIT_DIFF_MONITOR_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "bit_diff_item.svh"

// Here we create a "virtual" base class that will contain functionality
// required by all monitors. A virtual class cannot be instantiated directly
// and is only use by other classes to inherit common functionality.
//
// This class contains the virtual interface, which it obtains via the
// config_db during the build phase.
virtual class bit_diff_base_monitor extends uvm_monitor;
    // The following macro is needed by every class derived from a uvm_compontent
    // in order to register the class with the UVM factory.
    `uvm_component_utils(bit_diff_base_monitor)

    virtual bit_diff_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual bit_diff_if)::get(this, "", "vif", vif)) `uvm_fatal("NO_VIF", {"Virtual interface must be set for: ", get_full_name()});
    endfunction

    pure virtual task run_phase(uvm_phase phase);
endclass


// The done monitor inherits from the base monitor to acquire the interface.
// It then declares a port that is used to communicate with the scoreboard,
// while also implementing the detection of done events during the run phase.
class bit_diff_done_monitor extends bit_diff_base_monitor;
    `uvm_component_utils(bit_diff_done_monitor)

    uvm_blocking_put_port #(int) done_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        done_port = new("done_port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    // The done monitor by using the interface's wait_for_done task.
    task run_phase(uvm_phase phase);
        forever begin
            // Use the interface's task to detect when an execution has finished.
            vif.wait_for_done();
            //`uvm_info("DONE_MONITOR", "Detected completed execution", UVM_LOW)

            // Send the result to the scoreboard via through the done port.
            done_port.put(vif.result);
        end
    endtask
endclass


class bit_diff_start_monitor extends bit_diff_base_monitor;
    `uvm_component_utils(bit_diff_start_monitor)

    uvm_blocking_put_port #(int) start_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        start_port = new("start_port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            // Use the interface's task to detect when an execution has started.
            vif.wait_for_start();
            //`uvm_info("START_MONITOR", $sformatf("Detected new execution for data=%0h", vif.data), UVM_LOW)
            
            // Send the input to the scoreboard via the start_port.
            start_port.put(vif.data);
        end
    endtask
endclass


`endif
