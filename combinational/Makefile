# Author(s): 
# 	Wes Piard
#
# Purpose: Invokes simulations using Modelsim or VCS with options for debugging to
#	automatically invoke the simulators' GUIs.
#
# Usage:
#	The default simulator is Modelsim, and by default, debugging (opening the GUI) is disabled.
#
# 	For example, to run the `mux2x1_tb` testbench using Modelsim without invoking the GUI, run the
# 	command `make TOP=mux2x1_tb`. This will compile the relevant files and run the simulation. 
# 	If you would like to view the waveform to view the circuit's functionality, or to debug something
# 	that isn't working, then add the DEBUG flag to the command: `make TOP=mux2x1_tb DEBUG=1`.
#
#	To use VCS instead of Modelsim, you can run the same commands, but add `SIMULATOR=vcs`, e.g.,
#	`make SIMULATOR=vcs TOP=mux2x1_tb` or `make SIMULATOR=vcs TOP=mux2x1_tb DEBUG=1`. Note that
#	when debugging with VCS, the GUI that opens is actually a different program called `Verdi`.


# Modelsim is the default simulator if one isn't specified when calling `make`.
SIMULATOR?=modelsim

# By default, simulations will run with no debug visibility and only via the
# command line. 
DEBUG?=0

# Lists of valid simulators and testbench modules used for error checking.
VALID_SIMULATORS=modelsim vcs
VALID_MODULES=add_tb alu_tb mult_tb mux2x1_tb priority_encoder_4in_tb priority_encoder_tb

# Defined in the `check` target. Based on the testbench specified by the user.
FILES?=


sim: check
ifeq ($(SIMULATOR),modelsim)
	vlib work
	vlog -sv -timescale="1ns/10ps" $(FILES)
ifeq ($(DEBUG),0)
	vsim -64 -c -do "run -all; exit" $(TOP)
else
	vopt +acc add_tb -o debug_sim
	vsim -64 debug_sim
endif
else
ifeq ($(DEBUG),0)
	vcs -full64 -R -top $(TOP) -sverilog -timescale="1ns/10ps" $(FILES)
else
	vcs -full64 -kdb -debug_access+r -top $(TOP) -sverilog -timescale="1ns/10ps" $(FILES)
	./simv -ucli -i gen_db.tcl
	verdi -ssf novas.fsdb
endif
endif


check: 
# Check if the user specified a valid simulator.
ifeq ($(filter $(VALID_SIMULATORS),$(SIMULATOR)),)
	$(error Invalid SIMULATOR specified! Valid options are `modelsim` or `vcs`.)
endif

# Check if the user specified a valid top-level testbench module.
ifeq ($(filter $(VALID_MODULES),$(TOP)),)
	$(error Invalid TOP specified. Valid options are `mux2x1_tb` `add_tb`, etc.)
endif

# Set the FILES variable, which is used when compiling the desgins. It will essentially 
# be the list of files to be compiled by the simulation tool.
ifeq ($(TOP),mux2x1_tb)
	$(eval FILES=mux2x1.sv mux2x1_tb.sv)
else ifeq ($(TOP),add_tb)
	$(eval FILES=add.sv add_tb.sv)
else ifeq ($(TOP),alu_tb)
	$(eval FILES=alu_pkg.sv alu.sv alu_tb.sv)
else ifeq ($(TOP),mult_tb)
	$(eval FILES=mult.sv mult_tb.sv)
else ifeq ($(TOP),priority_encoder_tb)
	$(eval FILES=priority_encoder.sv priority_encoder_tb.sv)
else ifeq ($(TOP),priority_encoder_4in_tb)
	$(eval FILES=priority_encoder_4in.sv priority_encoder_4in_tb.sv)
else
	$(error "Invalid top-level module. Valid examples are `mux2x1_tb, add_tb, etc.`")
endif

# If debug is specified, then a valid DISPLAY must be connected to open the GUIs.
ifeq ($(DEBUG),1)
ifndef DISPLAY
	$(error DISPLAY not defined. Make sure you are running with X11 forwarding enabled if connected via SSH.)
endif
endif


clean:
# Remove VCS and Modelsim simulation artifacts
	rm -rf csrc/ simv.daidir/ simv ucli.key vc_hdrs.h
	rm -rf *.fsdb *.conf *.rc *.log verdiLog/ verdi_config_file
	rm -rf work/ transcript *.wlf
