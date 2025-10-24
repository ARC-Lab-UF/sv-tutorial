package ram_init_demo_pkg;

    localparam logic [7:0] RAM_INIT_DEMO_ARRAY[64] =
    '{
        0: 'hFF,
        1: 'hFF,
        2: 'hFF,
        3: 'hFF,
        4: 'hFF,
        5: 'hFF,
        6: 'hFF,
        7: 'hFF,
        8: 'h10,
        9: 'h12,
        10: 'h14,
        11: 'h16,
        12: 'h18,
        13: 'h1A,
        14: 'h1C,
        15: 'h1E,
        16: 'hAA,
        17: 'h55,
        18: 'h77,
        19: 'hAA,
        20: 'h55,
        21: 'h77,
        22: 'hAA,
        23: 'h55,
        24: 'h1D,
        25: 'h10,
        26: 'h19,
        27: 'h1B,
        28: 'h16,
        29: 'h18,
        30: 'h1D,
        31: 'h15,
        32: 'hBC,
        33: 'hA0,
        34: 'h55,
        default: 'h0
    };

endpackage
