// ALU in this case performs the following operations:
// Addition --> when (sel = 2'b00)
// Subtraction --> when (sel = 2'b01)
// AND --> when (sel = 2'b10)
// OR --> when (sel = 2'b11)
// for this case, we assume that the status flags can be
// set to any value for "and" "and" or operations.
module alu_bad
#(parameter WIDTH)
(
    input logic [WIDTH-1:0] in0,
    input logic [WIDTH-1:0] in1,
    input logic [2:0] sel,
    output logic [WIDTH-1:0] out,
    output logic neg, pos, zero
);

always_comb begin
    case (sel)
        // addition
        2'b00: begin
            out = in0 + in1;
            if (out == 0)begin
                pos = 1'b0;
                neg = 1'b0;
                zero = 1'b1;
                end
            else if (out > 0)begin
                pos = 1'b1;
                neg = 1'b0;
                zero = 1'b0;
                end
            else begin
                pos = 1'b0;
                neg = 1'b1;
                zero = 1'b0;
                end
            end
        // subtraction
        2'b01:begin
            out = in0 - in1;
            if (out == 0)begin
                pos = 1'b0;
                neg = 1'b0;
                zero = 1'b1;
                end
            else if (out > 0)begin
                pos = 1'b1;
                neg = 1'b0;
                zero = 1'b0;
                end
            else begin
                pos = 1'b0;
                neg = 1'b1;
                zero = 1'b0;
                end
            end 
        // and
        2'b10: out = in0 & in1;
        // or
        2'b11: out = in0 | in1;
        // in the case of and and or operations,
        // the statu flags neg, pos, and zero are not set to anything,
        // which means they will preserve whatever the previous value was.
        // This is not possible for combinational logic, and comb logic does
        // not preserve the previous states. That is something sequential
        // logic does. Synthesis tools will give a warning. And it will
        // create a latch to preserve the previous states of status flags.
        // For fpga's we absolutely want to avoid latches. 
        // since weare using always_comb, the synthesis tooll will
        // throw an error due to the presence of latches. 
    endcase
end
endmodule


module alu_good
#(parameter WIDTH)
(
    input logic [WIDTH-1:0] in0,
    input logic [WIDTH-1:0] in1,
    input logic [2:0] sel,
    output logic [WIDTH-1:0] out,
    output logic neg, pos, zero
);

always_comb begin
    case (sel)
        // addition
        2'b00: begin
            out = in0 + in1;
            if (out == 0)begin
                pos = 1'b0;
                neg = 1'b0;
                zero = 1'b1;
                end
            else if (out > 0)begin
                pos = 1'b1;
                neg = 1'b0;
                zero = 1'b0;
                end
            else begin
                pos = 1'b0;
                neg = 1'b1;
                zero = 1'b0;
                end
            end
        // subtraction
        2'b01:begin
            out = in0 - in1;
            if (out == 0)begin
                pos = 1'b0;
                neg = 1'b0;
                zero = 1'b1;
                end
            else if (out > 0)begin
                pos = 1'b1;
                neg = 1'b0;
                zero = 1'b0;
                end
            else begin
                pos = 1'b0;
                neg = 1'b1;
                zero = 1'b0;
                end
            end 
        // and
// Synthesis coding guidelines:
// all paths through the always block must define all outputs,
// otherwise the synthesis tool will throw an error becase latches will be automatically
// inferred in the design in those paths that do not define all outputs explicitly.        
        2'b10: begin 
            out = in0 & in1;
            if (out == 0)begin
                    pos = 1'b0;
                    neg = 1'b0;
                    zero = 1'b1;
                    end
                else if (out > 0)begin
                    pos = 1'b1;
                    neg = 1'b0;
                    zero = 1'b0;
                    end
                else begin
                    pos = 1'b0;
                    neg = 1'b1;
                    zero = 1'b0;
                    end
            end
        // or
        2'b11: begin 
            out = in0 | in1;
            if (out == 0)begin
                    pos = 1'b0;
                    neg = 1'b0;
                    zero = 1'b1;
                    end
                else if (out > 0)begin
                    pos = 1'b1;
                    neg = 1'b0;
                    zero = 1'b0;
                    end
                else begin
                    pos = 1'b0;
                    neg = 1'b1;
                    zero = 1'b0;
                    end
            end
    endcase
end
endmodule

module alu_good1
#(parameter WIDTH)
(
    input logic [WIDTH-1:0] in0,
    input logic [WIDTH-1:0] in1,
    input logic [2:0] sel,
    output logic [WIDTH-1:0] out,
    output logic neg, pos, zero
);

always_comb begin
    case (sel)
        2'b00: out = in0 + in1;
        2'b01: out = in0 - in1;
        2'b10: out = in0 & in1;
        2'b11: out = in0 | in1;
    endcase    
    if (out == 0)begin
        pos = 1'b0;
        neg = 1'b0;
        zero = 1'b1;
    end
    else if (out > 0)begin
        pos = 1'b1;
        neg = 1'b0;
        zero = 1'b0;
    end
    else begin
        pos = 1'b0;
        neg = 1'b1;
        zero = 1'b0;
    end
end
endmodule