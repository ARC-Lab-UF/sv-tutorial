//format: direction kind type name
// default kind of input is wire
// default kind of output is variable
    

module mux2_1_assign(
    input logic in0,
    input logic in1,
    input logic sel,
    output logic out
);
    assign out = sel ? in1 : in0;
endmodule


module mux2_1_if(
    input logic in0,
    input logic in1,
    input logic sel,
    output logic out
);

    always @(*) begin
        if(sel == 1'b1) begin
            out = in1;
        end else begin
            out = in0;
        end
    end
endmodule


module mux2_1_if2(
    input logic in0,
    input logic in1,
    input logic sel,
    output logic out
);
    always_comb begin
        if(sel == 1'b1) begin
            out = in1;
        end else begin
            out = in0;
        end
    end  
endmodule


module mux2_1_case(
    input logic in0,
    input logic in1,
    input logic sel,
    output logic out
);
    always_comb begin
        case(sel)
            1'b0: out = in0;
            1'b1: out = in1;
        endcase
    end
endmodule