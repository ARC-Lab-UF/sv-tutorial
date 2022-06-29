// four input priority encoder
//Priority Encoders take all of their data inputs one at a time and 
//converts them into an equivalent binary code at its output
module priority_encoder_4in_if(
    input logic [3:0] inputs,
    output logic [1:0] result,
    output logic valid
);
    always_comb begin
        if (inputs[3] == 1'b1) begin
            result = 2'b11;
            valid = 1'b1;
            end
        else if (inputs[2] == 1'b1) begin
            result = 2'b10;
            valid = 1'b1;
        end
        else if (inputs[1] == 1'b1) begin
            result = 2'b01;
            valid = 1'b1;
        end
        else if (inputs[0] == 1'b1) begin
            result = 2'b00;
            valid = 1'b1;
        end
        else begin
            result = 2'b00;
            valid = 1'b0;
        end
    end
endmodule


module priority_encoder_4in_case1(
    input logic [3:0] inputs,
    output logic [1:0] result,
    output logic valid
);
    always_comb begin
        valid = 1'b0;
        case(inputs)
            4'b0000: begin
                result = 2'b00;
                valid = 1'b0;
            end
            4'b0001: result = 2'b00;
            4'b0010, 4'b0011: result = 2'b01;
            4'b0100, 4'b0101, 4'b0110, 4'b0111: result = 2'b10;
            4'b1000, 4'b1001, 4'b1010, 4'b1011: result = 2'b11;
    end
endmodule



module priority_encoder_4in_case2(
    input logic [3:0] inputs,
    output logic [1:0] result,
    output logic valid
);
always_comb begin
    valid = 1'b1;
    casez(inputs)
    //casez is used when we only care about certain bits and dont care
    //about the rest of them. The ones we dont care are marked with ?
    //synthesis will happen exactly like case statements.
    4'b1???: result = 2'b11;
    4'b01??: result = 2'b10;
    4'b001?: result = 2'b01;
    4'b0001: result = 2'b00;
    4'b0000: begin result = 2'b00; valid = 1'b0; end
    endcase
endmodule