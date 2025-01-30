// This package defines interface parameters that are needed for instantiations
// of classes, iterfaces, and modules. All other parameters can be passed around
// via the config DB, but the config DB cannot be used to provide class, module, 
// and interface parameters since those need to be known at compile time.
//
// We could make these parameters to the testbench module, but then we would 
// need to add parameters to the uvm_test classes. This is possible, but is 
// usually so tedious that using a package like this is an acceptable tradeoff.

package bit_diff_if_pkg;
    localparam int WIDTH = 16;
endpackage
