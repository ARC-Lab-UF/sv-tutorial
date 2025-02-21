// Greg Stitt
// University of Florida

// This package provides default widths for the data and sideband signals. This
// is very useful because all the components of the UVM agent will need a 
// default value. We don't want to hardcode those defaults in each component
// because if one changes, it will cause problems. Using the package ensures
// that all agent instances will use the same defaults.

package axi4_stream_pkg;

    localparam int DEFAULT_DATA_WIDTH = 16;
    localparam int DEFAULT_ID_WIDTH   = 4;
    localparam int DEFAULT_DEST_WIDTH = 4;
    localparam int DEFAULT_USER_WIDTH = 4;

    // Unlike the previous examples where we included the svh files everywhere
    // that a class was referenced (i.e., C++ style), we now instead use a 
    // recommendation from the "UVM Cookbook" and include all corresponding
    // includes in the package. Note they have to be specified in the correct
    // compilation order.
    //
    // This style is convenient because it specifies all files related to the
    // agent in one place, and it eliminates the need to include the files
    // in other locations. Because the package file must be compiled first,
    // all the includes will now be compiled at the same time.
    `include "axi4_stream_seq_item.svh"
    `include "axi4_stream_monitor.svh"
    `include "axi4_stream_driver.svh"
    `include "axi4_stream_sequencer.svh"
    `include "axi4_stream_agent.svh"

endpackage