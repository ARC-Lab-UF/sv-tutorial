// Greg Stitt
// University of Florida

// This module demonstrates a simple AXI4-stream multiplier. Note that it this
// is not how I would recommend implementing such a multiplier. This example
// is intentionally artificial to help demonstrate UVM practices without the 
// need for a complex DUT.
//
// The module has two streaming input ports, and one streaming output port.
// The input ports both have INPUT_WIDTH bits, and the output port has
// INPUT_WIDTH*2 bits.

module mult #(
    parameter int INPUT_WIDTH = 16,
    parameter bit IS_SIGNED   = 1'b0
) (
    input logic aclk,
    input logic arst_n,

    // AXI4 stream interface for each multiplier input.
    input  logic [            1:0] in_tvalid,
    output logic [            1:0] in_tready,
    input  logic [INPUT_WIDTH-1:0] in_tdata [2],

    // AXI4 stream interface for multiplier output
    output logic                     out_tvalid,
    input  logic                     out_tready,
    output logic [2*INPUT_WIDTH-1:0] out_tdata
);
    logic en;
    logic [INPUT_WIDTH*2-1:0] product_r;
    logic product_valid_r;

    initial if (INPUT_WIDTH % 8 != 0) $fatal(1, $sformatf("AXI requires INPUT_WIDTH (%0d) to be byte aligned", INPUT_WIDTH));

    // Enable/disable the pipeline. AXI streaming is a little weird and can't
    // simply stall on !out_tready. The spec says that a transmitter cannot
    // wait for tready to asser tvalid, so here we enable the pipeline anytime 
    // the output isn't valid. We only stall when !out_tready && out_tvalid.
    assign en = out_tready || !out_tvalid;

    // Each input port must wait for the other before accepting a new input.
    //
    // NOTE: while technically AXI-compliant, there are a few things I wouldn't
    // normally recommand. One potential problem is that ready is a function of 
    // en, which is a function of a downstream ready, etc. If you have 10 of 
    // these modules chained together, this ready logic creates a massive 
    // combinational logic chain that will limit clock frequencies. It is often 
    // best to "break" this ready chain with either FIFOs, which would be
    // expensive for just a multiplier, or by registering the ready flags, which
    // then requires skid buffers. For now, we'll keep it simple and leave in 
    // the timing bottleneck.
    //
    // Another problem is that an upstream AXI module could unknowingly create a 
    // combinational loop if its valid output is a function of this module's
    // ready output. Because our ready is a function of that valid, and that 
    // valid is a function of our ready, we have a loop. Again, this problem
    // could be fixed in multiple ways, such as registering the ready flag. 
    //
    // My suggested solution is to never have ready be a function of valid. This
    // makes it impossible to have a combinational loop, regardless of whether 
    // ready is combinational or registered. Similarly, I recommend making the
    // valid output a function that excludes ready. It is common for ready to
    // control the enable of a register that defines the valid output, so it is
    // ok to make the timing of valid dependent on ready, but I recommend 
    // defining the value of output independently from ready. For example, don't
    // clear valid because ready is 0. In fact, the AXI spec prohibits this.
    //
    // This unrecommended style was chose to avoid the need for other modules,
    // and to keep the latency of the multiplier to 1 cycle. Ultimately, these
    // problems are why you would likely never have just a multiplier in an
    // AXI streaming module. Maintaining AXI compliance and safe practices adds
    // overhead that should be amortized over larger amounts of logic.
    //
    // If I didn't care about latency and/or resources, I would just put a FIFO 
    // on each input and connect in_tready[i] to !fifo_full[i]. This is the 
    // safest practice since it decouples the ports from each other and makes
    // the ready logic independent of valid.

    assign in_tready[0] = en && in_tvalid[1];
    assign in_tready[1] = en && in_tvalid[0];

    always_ff @(posedge aclk) begin
        if (en) begin
            if (IS_SIGNED) product_r <= signed'(in_tdata[0]) * signed'(in_tdata[1]);
            else product_r <= in_tdata[0] * in_tdata[1];

            product_valid_r <= &in_tvalid;
        end

        if (!arst_n) begin
            product_valid_r <= 1'b0;
        end
    end

    assign out_tvalid = product_valid_r;
    assign out_tdata  = product_r;

endmodule
