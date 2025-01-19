// Greg Stitt
// University of Florida
//
// This file demonstrates how to use a loop to generate a structural pattern
// in a circuit. Specifically, it creates a ripple carry adder with a
// parameterized width by instantiating full adders in a loop.
//
// See ripple_carry_adder.pdf for an illustration of the schematic being
// created. Remember that all strucutural architectures should start from a
// schematic.


// Module: full_adder
// Description: A basic behavioral implementation of a full adder.

module full_adder (
    input  logic x,
    input  logic y,
    input  logic cin,
    output logic s,
    output logic cout
);
    // Specify the sum and carry out logic equations for a full adder.
    assign s = x ^ y ^ cin;
    assign cout = (x & y) | (cin & (x ^ y));

endmodule  // full_adder


// Module: ripple_carry_adder
// Description: A structural ripple carry adder with a parameter for width,
// built from the preceding full_adder module. Demonstrates how to use a
// generate statement and for loop.

module ripple_carry_adder #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] x,
    input  logic [WIDTH-1:0] y,
    input  logic             cin,
    output logic [WIDTH-1:0] sum,
    output logic             cout
);
    // Create an internal signal to store the carries between all full adders.
    // Note that this is WIDTH+1 bits to account for the overall carry out.
    logic [WIDTH:0] carry;

    // Connect the first carry to the carry in.
    assign carry[0] = cin;

    // Instantiate WIDTH separate full adders using a for loop, and connect them
    // into a ripple-carry by connecting the carry out from one full adder into
    // the carry in of the next.
    //
    // You can also use an if statement within a generate, but keep in mind that
    // the condition must be a function of constants and parameters. No dynamic
    // values can be used because the synthesis tool must resolve the condition
    // at compile time.
    generate
        for (genvar i = 0; i < WIDTH; i++) begin : ripple_carry_l
            full_adder FA (
                .x   (x[i]),
                .y   (y[i]),
                .s   (sum[i]),
                .cin (carry[i]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    // Connect the last carry to the carry out.
    assign cout = carry[WIDTH];

endmodule


module ripple_carry_adder2 #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] x,
    input  logic [WIDTH-1:0] y,
    input  logic             cin,
    output logic [WIDTH-1:0] sum,
    output logic             cout
);

    logic [WIDTH:0] carry;
    assign carry[0] = cin;

    // The generate statement is actually completely optional, but the for loop
    // must use a genvar. Keep in mind that this for loop is not inside an
    // always block, so the body can only make continuous assignments or module
    // instantiations.
    for (genvar i = 0; i < WIDTH; i++) begin : ripple_carry
        full_adder FA (
            .x   (x[i]),
            .y   (y[i]),
            .s   (sum[i]),
            .cin (carry[i]),
            .cout(carry[i+1])
        );
    end

    assign cout = carry[WIDTH];

endmodule

