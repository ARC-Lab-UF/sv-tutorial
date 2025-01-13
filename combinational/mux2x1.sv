// Greg Stitt
// University of Florida

// Module: mux2x1_assign
// Description: behavioral 2x1 mux using an assign statement.

module mux2x1_assign (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

    // VHDL DIFFERENCE:
    // Unlike VHDL, SystemVerilog's modules can't have multiple architectures. 
    // Each module defines one specific implementation. Alternatively, you can 
    // use parameters and if statements to define multiple implementations for a
    // single module.

    // Uses the ternary operator to conditionally assign output based on the
    // select input.
    assign out = sel == 1'b1 ? in1 : in0;

    // Or, assign out = sel ? in1 : in0;

endmodule  // mux2x1_assign


// Module: mux2x1_if
// Description: behavioral 2x1 mux using an if statement.

module mux2x1_if (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

    // always_comb is a process that executes any time the value of a signal 
    // that is read inside the process changes. In this case, changes to sel, 
    // in0, or in1 will cause the process to execute. 
    //
    // always_comb is an explicit way of specifying you want to describe
    // combinational logic. Because combinational logic outputs are a function
    // of the current inputs, the process executes to change the output any time
    // an input changes.
    //
    // VHDL_DIFFERENCE:
    // always_comb is equivalent to process(all) in VHDL 2008. For older versions
    // of VHDL, there isn't an equivalent and all input must be explicitly
    // specified in the sensitivity list. e.g. process(in0, in1, sel)

    always_comb begin
        if (sel == 1'b0) begin
            out = in0;
        end else begin
            out = in1;
        end
    end

endmodule  // mux2x1_if


// Module: mux2x1_if2
// Description: Alternative behavioral 2x1 mux using an if statement. 
// Demonstrates different SV constructs.

module mux2x1_if2 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

    // As an alternative to always_comb, we could use a more general "always
    // block." The @ specifies when the block should execute. The content inside
    // the () is the "sensitivity list", which is a list of events that trigger
    // the execution.

    always @(*) begin
        // Notice the lack of begin and end keywords. For single-line 
        // statements, begin/end can be omitted, similar to C/C++. For
        // multiple statements in the if/else bodies, you must use begin/end.	
        if (sel == 1'b0) out = in0;
        else out = in1;
    end

endmodule  // mux2x1_if2


// Module: mux2x1_if3
// Description: Alternative behavioral 2x1 mux using a non-blocking asssignments. 
// Demonstrates different SV constructs.

module mux2x1_if3 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);
    always @(*) begin
        // Here we use non-blocking assignments, which will be explained 
        // later. For this example, blocking and non-blocking 
        // will give the same results, but that will not always be the case.
        // Most people recommend avoiding non-blocking assignments in 
        // combinational logic for reasons we will revisit. Technically,
        // non-blocking assignments are perfectly fine for combinational logic
        // (VHDL signals only support non-blocking), but it is best that you
        // use blocking for combinational logic unless you have a very good
        // reason not to.
        if (sel == 1'b0) out <= in0;
        else out <= in1;
    end

    //
    // SYNTHESIS GUIDELINE: Use always_comb with blocking assignments when 
    // describing combinational logic. This example has nearly quivalent behavior, 
    // but always_comb can enable tools to report warnings or errors if if you 
    // accidentally introduce any sequential logic. It also makes the intent 
    // of the code explicit.
    //
    // COMMON INTERVIEW QUESTION: What is the difference between always_comb
    // and always @(*)?
    //
    // Answer: at time 0, always_comb always executes whereas always @(*) only
    // executes if the inputs change. There are also subtle differences when
    // functions are called within each. e.g.,:
    //
    // https://stackoverflow.com/questions/32778798/behavior-difference-between-always-comb-and-always

endmodule  // mux2x1_if3


// Module: mux2x1_case
// Description: behavioral 2x1 mux using a case statement.

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

            // Like C++, you can use a default:
            // default : out = ...
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
    // mux2x1_if3 mux (.*);
    // mux2x1_case mux (.*);

endmodule  // mux2x1
