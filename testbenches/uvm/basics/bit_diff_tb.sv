// Greg Stitt
// University of Florida

// This testbench is a simple example of how to use UVM. The testbench module
// itself simply creates an interface, instantiates the DUT, writes 
// simulation parameters to the UVM config database, and then starts a
// test.

// Before reading further, it is important to have a basic understanding of
// several key UVM concepts: phasing system, UVM Config DB, 
// These are summarized below.

// PHASING SYSTEM:
// The UVM phasing system helps synchronize the different stages of the 
// verification process by breaking it down into distinct phases, which helps
// ensure that all the components of the testbench interact in an orderly and 
// predictable manner during simulation.  These phases control when specific 
// actions should take place in the simulation lifecycle.
//
// While there are many different phases, some of them are not commonly used.
// In this example, we will focus on the most common stages.
//
// Build Phase: 
// This phase is where all objects are created and initialized. The testbench 
// components are instantiated during this phase.
//
// Connect Phase: The components that were created in the Build phase are 
// connected to each other. This typically includes connecting interfaces, 
// ports, and other communication paths between different testbench components.
//
// End of Elaboration Phase: This is where any final setup and checks are done 
// before the simulation starts.
//
// Run Phase: This is the main phase where the testbench actively performs the 
// stimulus generation, monitoring, driving, etc.
//
// Report Phase: The results of the verification process are generated and 
// reported, typically in the form of logs and reports, detailing coverage, 
// assertions, and any errors or mismatches detected.

// UVM CONFIGURATION DATABASE:
// The UVM Config DB (Configuration Database) is a central mechanism for 
// managing and sharing configuration data across different components of the 
// testbench. It allows different objects (like agents, environments, or 
// sequences) to communicate and share information in a flexible and decoupled
// way, without the need for direct dependencies between them. Ultimately, this
// database greatly reduces complexity and increases flexibility by not
// requiring explicit static dependencies between all testbench components.

// UVM Factory
// The UVM Factory is a central component in the UVM methodology that manages 
// the creation of objects in a testbench. It allows for dynamic object creation
// and is key to ensuring flexibility and reusability in verification 
// environments. The factory allows you to override default object creation 
// behaviors, enabling custom configurations or parameterization at runtime.
//
// In general, factories are a design pattern that help manage complexity in object 
// creation. They are most beneficial in large, complex projects where you have
// many object types, intricate creation logic, and dynamic configuration 
// requirements. In smaller projects, the benefits might not be immediately
// obvious, and direct instantiation might be sufficient. The value of 
// factories becomes more apparent as the project scales and the need for 
// maintainability, extensibility, and flexibility increases.

// This header and package will be included in just about every file within
// a UVM testbench.
`include "uvm_macros.svh"
import uvm_pkg::*;

// Include the definition of the test we are going to run. We'll see a better
// way of doing this in later examples.
`include "bit_diff_simple_test.svh"

// This package defines parameters that are needed to define different class,
// interface, and module parameters. Other parameters will be distributed via
// the config DB, but the DB uses run-time values which can't be used for
// class, interface, and module parameters. We could alternatively parameterize
// the test class and distribute the parameters to all other components via
// the UVM class hierarchy, but doing so is quite tedious and usually not worth
// the effort.
import bit_diff_if_pkg::*;

`timescale 1 ns / 100 ps

module bit_diff_tb #(
    parameter int NUM_TESTS = 10000
);
    bit clk = 1'b0;

    // Note that I'm not using my normal template here. The reason is that
    // it is pretty widely accepted for complex testbenches to just call
    // $finish to end the simulation, so with UVM, I generally don't bother
    // with a more natural termination. UVM has a phasing system where after
    // all the phases complete, the UVM framework calls $finish itself:
    //
    // https://github.com/accellera-official/uvm-core/blob/main/src/base/uvm_root.svh
    //
    //

    always #5 clk <= ~clk;

    // Create an interface that will be used within UVM.
    // NOTE: We are using the default WIDTH for now. We'll see why in a later
    // example. Using a parameterized interface in UVM introduces a number of
    // complications that require lengthy explanations. Basically, the interface
    // width will have to be passed to every class using the interface, which
    // is harder than you would expect. We work around that challenge by having
    // the interface use a default value as defind by bit_diff_if_pkg::WIDTH, 
    // which we can refer to across all modules, interfaces, and classes.
    bit_diff_if intf (clk);

    // Instantiate the DUT.
    bit_diff #(
        // Use the WIDTH as defined in the interface package. We'll see a more
        // flexible way of doing this in later examples.
        .WIDTH(bit_diff_if_pkg::WIDTH)
    ) DUT (
        .clk   (intf.clk),
        .rst   (intf.rst),
        .go    (intf.go),
        .data  (intf.data),
        .result(intf.result),
        .done  (intf.done)
    );

    // We could potentially treat the reset as a UVM sequence as part of a 
    // detailed test of a complex reset mechanism, but in most cases you will
    // still reset the DUT in the testbench itself. The driver could also 
    // implicitly reset the interface, but I don't like that approach since
    // the driver generally is supposed to simply drive transactions it receives.
    initial intf.reset(5);

    // Initial the parameters of the simulation. Note that we aren't explicitly
    // instantiating any of the UVM classes and then passing parameters to those
    // classes. Instead, we write the parameters that will be needed across all
    // the classes to the config_db, allowing them to be read from multiple 
    // places.
    initial begin
        $timeformat(-9, 0, " ns");

        // Store a virtual interface (i.e., a pointer to the interface) in the 
        // config_db under the name "vif".
        uvm_config_db#(virtual bit_diff_if)::set(uvm_root::get(), "*", "vif", intf);

        // Store the number of tests to the config_db under the name "num_tests".
        uvm_config_db#(int)::set(uvm_root::get(), "*", "num_tests", NUM_TESTS);

        // Uncomment to generate a VCD file of the sim behavior.
        //$dumpfile("dump.vcd");
        //$dumpvars;
    end

    // Here we specify which specific test we want to run. run_test() starts 
    // a UVM test. If a parameter is provided, it should be a string specifying
    // the name of the class that corresponds to the test. In general, it is
    // better to not provide a parameter, in which case run_test uses the
    // UVM_TESTNAME environment variable that you can set from the command line, 
    // allowing you to run different tests with the same testbench.
    //
    // Also, by not specifying a parameter, you can actually compile all the 
    // code and then run different combinations of tests to help achieve 100%
    // coverage. Large applications can take a long time to compile, even for
    // simulation, so it can be quite useful to run a bunch of tests in sequence
    // without having to recompile.
    initial begin
        run_test("bit_diff_simple_test");
    end

    // SVAs can be conveniently combined with UVM by using the uvm_error macro 
    // to record errors. `uvm_error maintains a global error count, no matter 
    // where it is called from. So, as opposed to these assertions causing 
    // separate errors from the scoreboard, they just add to the error counts 
    // from other places.
    assert property (@(posedge intf.clk) disable iff (intf.rst) intf.go && intf.done |=> !intf.done)
    else `uvm_error("ASSERT", "Done not cleared one cycle after go.");

    assert property (@(posedge intf.clk) disable iff (intf.rst) $fell(intf.done) |-> $past(intf.go, 1))
    else `uvm_error("ASSERT", "Done was cleared without go being asserted");

endmodule
