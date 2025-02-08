// Greg Stitt
// University of Florida

// The scoreboard waits to receive an input from the start monitor and the 
// actual output from the done monitor. It then uses the input to compute the
// expected output. Finally, it compares the expected output with the actual
// output, and reports errors if there are any differences.

`ifndef _MULT_SCOREBOARD_SVH_
`define _MULT_SCOREBOARD_SVH_

`include "uvm_macros.svh"
import uvm_pkg::*;

import mult_if_pkg::*;

class mult_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(mult_scoreboard)

   

endclass

`endif
