module adder
    #(parameter  int WIDTH)
    (
        input logic [WIDTH-1:0] in1;
        input logic [WIDTH-1:0] in2;
        output logic [WIDTH-1:0] sum;
    );

    // if signed/unsigned in not specified, SV defaults to unsigned. 
    // so the below statement would be an unsigned addition.
    assign sum = in1 + in2;
endmodule


module adder_comb
    #(parameter  int WIDTH)
    (
        input logic [WIDTH-1:0] in1;
        input logic [WIDTH-1:0] in2;
        output logic [WIDTH-1:0] sum;
    );
    always_comb begin
        sum = in1 + in2;
    end
endmodule

module adder_cout_bad
    #(parameter  int WIDTH = 8)
    (
        input logic [WIDTH-1:0] in1;
        input logic [WIDTH-1:0] in2;
        output logic [WIDTH-1:0] sum;
        output logic carryout;
    );
    logic [WIDTH:0] full_sum;
    // the below combinational block will not work correctly
    // because the values of fullsum, sum, and carryout
    // will be updated at the end of every always_comb block end.
    // So the values of sum and carryout in the correct cycle will be
    // equal to the correct value of the previous values of in1 and in2.
    
    // = is the blocking operator.
    // <= is the non blocking operator. This behaves like a signal in VHDL.
    // Signals in VHDL do not get their values until the end of the process
    always_comb begin
        full_sum <= in1 + in2;
        sum <= full_sum[WIDTH-1:0];
        carryout <= full_sum[WIDTH];
    end
endmodule

module adder_cout1
    #(parameter  int WIDTH = 8)
    (
        input logic [WIDTH-1:0] in1;
        input logic [WIDTH-1:0] in2;
        output logic [WIDTH-1:0] sum;
        output logic carryout;
    );
    logic [WIDTH:0] full_sum;
    //  blocking operators are used below. They work similarly to variables in VHDL.
    // This means nothing else executes until the variable in execution to be updated
    // gets the new value. So the following lines of code is not executed until
    // the current variable is updated with the latest value

    // Whenever we want something to behave like a variable in SV,
    // we use blocking operators.
    always_comb begin
        full_sum = in1 + in2;
        sum = full_sum[WIDTH-1:0];
        carryout = full_sum[WIDTH];
    end
endmodule

// general coding guidelines:
// Always good practice to use blocking operators in combinational logic
// Always good practice to use non blocking operators in sequential logic

// below is the example of how to implement
// an adder in SV
module adder_cout_sv_only
    #(parameter  int WIDTH = 8)
    (
        input logic [WIDTH-1:0] in1;
        input logic [WIDTH-1:0] in2;
        output logic [WIDTH-1:0] sum;
        output logic carryout;
    );
 assign {carryout,sum} = in1 + in2;
endmodule