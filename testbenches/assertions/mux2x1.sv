// Greg Stitt
// University of Florida

module mux2x1_assign (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);
    assign out = sel == 1'b1 ? in1 : in0;
endmodule  // mux2x1_assign


module mux2x1_if (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);
    always_comb begin
        if (sel == 1'b0) out = in0;
        else out = in1;
    end
endmodule  // mux2x1_if


module mux2x1_if2 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);
    always @(*) begin
        if (sel == 1'b0) out <= in0;
        else out <= in1;
    end
endmodule  // mux2x1_if2


module mux2x1_case (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

    always_comb begin
        case (sel)
            1'b0: out = in0;
            1'b1: out = in1;
        endcase
    end
endmodule  // mux2x1_case


// Module: mux2x1
// Description: Top-level module, which is only required if this file is
// specified as the top-level module in a synthesis tool. In that case, 
// synthesis tools look for a module with the same name as the file.

module mux2x1 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

    // Change the module name here to synthesize other modules.
    // NOTE: This syntax will be explained in structurual architectures. Feel
    // free to ignore for now.

    mux2x1_assign mux (.*);
    // mux2x1_if mux (.*);
    // mux2x1_if2 mux (.*);
    // mux2x1_case mux (.*);

endmodule  // mux2x1
