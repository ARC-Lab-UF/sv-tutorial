
#modelsim is the default simulator if one isn't specified when calling `make`
SIMULATOR?=modelsim
DEBUG?=0

VALID_SIMULATORS=modelsim vcs
VALID_MODULES=add_tb alu_tb mult_tb mux2x1_tb priority_encoder_4in_tb priority_encoder_tb
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
	./simv -gui
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
