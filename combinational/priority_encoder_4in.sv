// Greg Stitt
// University of Florida

// Synthesis notes:
// All modules confirmed to synthesize in:
// Vivado 2024.2
// Quartus Prime Pro 23.1.0 (older versions did not support unique0 construct)

// Module: priority_encoder_4in_if
// Description: implements a 4-input (2-output) priority encoder using an if
// statement, with a valid output that is asserted when any of the inputs are
// asserted.

module priority_encoder_4in_if (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        // By default, assert valid. For all input combinations but 1, valid is
        // asserted, so this saves some code.
        valid = 1'b1;

        // Use an if statement to encode the priority.
        if (inputs[3]) result = 2'b11;
        else if (inputs[2]) result = 2'b10;
        else if (inputs[1]) result = 2'b01;
        else if (inputs[0]) result = 2'b00;
        else begin
            valid  = 1'b0;
            result = 2'b00;
        end

    end
endmodule  // priority_encoder_4in_if


// Module: priority_encoder_4in_case
// Description: An alternative implementation that uses a case statement.

module priority_encoder_4in_case1 (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        valid = 1'b1;

        // A basic case statement doesn't have a natural notion of priority, so we
        // need to define outputs for all input combinations.
        case (inputs)
            4'b0000: begin
                result = 2'b00;
                valid  = 1'b0;
            end
            4'b0001: result = 2'b00;
            4'b0010: result = 2'b01;
            4'b0011: result = 2'b01;
            4'b0100: result = 2'b10;
            4'b0101: result = 2'b10;
            4'b0110: result = 2'b10;
            4'b0111: result = 2'b10;
            4'b1000: result = 2'b11;
            4'b1001: result = 2'b11;
            4'b1010: result = 2'b11;
            4'b1011: result = 2'b11;
            4'b1100: result = 2'b11;
            4'b1101: result = 2'b11;
            4'b1110: result = 2'b11;
            4'b1111: result = 2'b11;
        endcase
    end
endmodule  // priority_encoder_4in_case1


// Module: priority_encoder_4in_case2
// Description: A slightly simplified implementation with a case statement.

module priority_encoder_4in_case2 (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        valid = 1'b1;

        // Here we combine multiple cases to slightly simply the description.
        case (inputs)
            4'b0000: begin
                result = 2'b00;
                valid  = 1'b0;
            end
            4'b0001: result = 2'b00;
            4'b0010, 4'b0011: result = 2'b01;
            4'b0100, 4'b0101, 4'b0110, 4'b0111: result = 2'b10;
            4'b1000, 4'b1001, 4'b1010, 4'b1011, 4'b1100, 4'b1101, 4'b1110, 4'b1111: result = 2'b11;
        endcase
    end
endmodule  // priority_encoder_4in_case2


// Module: priority_encoder_4in_case_inside
// Description: A greatly simplified implementation with a case statement.

module priority_encoder_4in_case_inside (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        valid = 1'b1;

        // By using "case inside," we can specify ranges of values for each case.
        case (inputs) inside
            4'b0000: begin
                result = 2'b00;
                valid  = 1'b0;
            end
            4'b0001: result = 2'b00;
            [4'b0010 : 4'b0011]: result = 2'b01;
            [4'b0100 : 4'b0111]: result = 2'b10;
            [4'b1000 : 4'b1111]: result = 2'b11;
        endcase
    end
endmodule  // priority_encoder_4in_case_inside


// Module: priority_encoder_4in_casez
// Description: A simplified case statement implementation using wildcards.

module priority_encoder_4in_casez (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        valid = 1'b1;

        // The casez statement allows for wildcard (i.e. don't care) inputs by
        // using a ?
        casez (inputs)
            4'b1???: result = 2'b11;
            4'b01??: result = 2'b10;
            4'b001?: result = 2'b01;
            4'b0001: result = 2'b00;
            4'b0000: begin
                result = 2'b00;
                valid  = 1'b0;
            end
        endcase
    end
endmodule  // priority_encoder_4in_casez


// Module: priority_encoder_4in_case_unique
// Description: A small extension that uses unique to guarantee no repeated cases.

module priority_encoder_4in_case_unique (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    always_comb begin
        valid = 1'b1;

        // "Unique" is a keyword added to the 2009 SV standard that is quite useful.
        // It adds two constraints that are checked by both simulation and synthesis.
        // The first is that the case expression only matches one case item. In other
        // words, you couldn't do something like:
        //
        // 4'b1000: result = 2'11;
        // 4'b1000: result = 2'10;
        //
        // While it would be incredibly weird to do that on purpose, you can easily
        // come up with two case items using wildcards that have overlap. Without the
        // unique keyword, that overlap would compile fine. With unique, you should get
        // errors or warnings (although some tools still annoying ignore it).
        //
        // The second constraint is that all paths are defined, meaning if it encounters
        // a case item not covered by the case expression, it will report an error.
        // This constraint is usually a good idea to avoid latches, since if there is a
        // path through a process that doesn't define an output, it causes a latch.
        // Unique doesn't guarantees all paths through the case are defined. It doesn't
        // guarantee there are no latches, but it is a good practice that helpes avoid
        // them.
        unique casez (inputs)
            4'b1???: result = 2'b11;
            4'b01??: result = 2'b10;
            4'b001?: result = 2'b01;
            4'b0001: result = 2'b00;
            4'b0000: begin
                result = 2'b00;
                valid  = 1'b0;
            end
        endcase
    end
endmodule  // priority_encoder_4in_case_unique


// Module: priority_encoder_4in_case_unique0
// Description: A small extension that uses unique0 to guarantee no repeated cases, while
// allowing for undefined case items.

module priority_encoder_4in_case_unique0 (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);
    // On some rare ccasions, you might want to ensure uniqueness of case items, 
    // but don't need definitions of all case items. In these situations, you
    // can use "unique0" instead of "unique."
    //
    // For example, in the following process, the first two statements 
    // act as defaults that obviate case item 4'b0000. The unique constraint
    // would fail, but unique0 handles what we intended.
    //
    // This is a largely synthetic example. There is no good reason to use unique0 here 
    // since it is less concise. It is simply intended for explanation.
    //  
    // In general, I would avoid case statements that don't define all case items.
    // 
    // NOTE: Vivado still reports linter warnings about incomplete paths, even when
    // using unique0, so tool support is likely lacking elsewhere too.
    //
    // Quartus Prime Pro 

    always_comb begin
        result = 2'b00;
        valid  = 1'b0;

        unique0 casez (inputs)
            4'b1???: begin
                result = 2'b11;
                valid  = 1'b1;
            end
            4'b01??: begin
                result = 2'b10;
                valid  = 1'b1;
            end
            4'b001?: begin
                result = 2'b01;
                valid  = 1'b1;
            end
            4'b0001: begin
                result = 2'b00;
                valid  = 1'b1;
            end
        endcase
    end
endmodule  // priority_encoder_4in_case_unique0


// Module: priority_encoder_4in
// Description: A top-level module that can be used to change the module used
// for synthesis and simulation.

module priority_encoder_4in (
    input  logic [3:0] inputs,
    output logic       valid,
    output logic [1:0] result
);

    // Uncomment the desired module for synthesis.
    priority_encoder_4in_if pe (.*);
    //priority_encoder_4in_case1 pe (.*);
    //priority_encoder_4in_case2 pe (.*);
    //priority_encoder_4in_case_inside pe (.*);
    //priority_encoder_4in_casez pe (.*);
    //priority_encoder_4in_case_unique pe (.*);
    //priority_encoder_4in_case_unique0 pe (.*);
endmodule

