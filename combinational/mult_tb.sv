// Greg Stitt
// University of Florida

// Module: mult_tb
// Description: Testbench for the different mult modules in mult.sv. Change
// the module that is instantiated in the mult module to test different modules.

module mult_tb #(
    parameter int NUM_TESTS   = 1000,
    parameter int INPUT_WIDTH = 16
);
    logic [INPUT_WIDTH-1:0] in0, in1;
    logic [INPUT_WIDTH*2-1:0] product_signed, product_unsigned;

    // Apparently SV doesn't allow the .* operator for parameters, only ports.
    mult #(
        .IS_SIGNED  (1'b1),
        .INPUT_WIDTH(INPUT_WIDTH)
    ) DUT_SIGNED (
        .product(product_signed),
        .*
    );

    mult #(
        .IS_SIGNED  (1'b0),
        .INPUT_WIDTH(INPUT_WIDTH)
    ) DUT_UNSIGNED (
        .product(product_unsigned),
        .*
    );

    initial begin

        logic [INPUT_WIDTH*2-1:0] correct_product_signed, correct_product_unsigned;

        for (int i = 0; i < NUM_TESTS; i++) begin
            in0 <= $urandom;
            in1 <= $urandom;
            #10;
            correct_product_signed   = signed'(in0) * signed'(in1);
            correct_product_unsigned = in0 * in1;

            if (product_signed != correct_product_signed)
                $error(
                    "[%0t]: signed product = %d instead of %d.",
                    $realtime,
                    product_signed,
                    correct_product_signed
                );

            if (product_unsigned != correct_product_unsigned)
                $error(
                    "[%0t]: unsigned product = %d instead of %d.",
                    $realtime,
                    product_unsigned,
                    correct_product_unsigned
                );
        end

        $display("Tests completed.");
    end
endmodule  // mult_tb
