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

endpackage