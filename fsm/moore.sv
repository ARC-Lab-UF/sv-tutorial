// Greg Stitt
// University of Florida

// The following example illustrates two models that I would recommend for
// creating a finite state machine (FSM), which I refer to as the 
// 1-process/block and 2-process/block models. The 1-process model is slightly 
// easier, but has the disadvantage of having registers/flip-flops on all 
// outputs, which adds one cycle of latency. The 2-process model requires a 
// little more code, but is more flexible. When timing/area are not a concern, 
// the 1-process model can save a little bit of time, but I would still 
// recommend using the 2-process model. Once you get used to it, it requires 
// only a minor amount of additional effort, and in my opinion is much easier 
// to debug.

// The following example implements the Moore FSM illustrated in fsm.pdf. A
// Moore FSM has outputs that are solely a function of the current state.
// Note that you should always draw the FSM first and then convert it to code.

// Module: moore_1p
// Description: This module implements the Moore FSM shown in fsm.pdf using
// the 1-process/block model. It is important to note that the 1-process model
// will delay all outputs by 1 cycle due to the extra register. This register
// has its uses (e.g. preventing glitches), but in general is problematic for
// any circuit requiring control signals within the same cycle.

module moore_1p (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [3:0] out
);
    // In SV, you can define states in many ways, but I recommend creating
    // your own state type using an enum. The advantage of this approach is
    // that it allows you to give state meaningful names (as opposed to values).
    // Those names then show up in simulation, which is much easier to track.
    // Also, with this enum approach, we are leaving it to the synthesis tool
    // to come up with the state encoding, which is usually a good idea.

    /*typedef enum       {
		       STATE0,
		       STATE1,
		       STATE2,
		       STATE3
		       } state_t;*/

    // By default, SV uses a signed integer type for the enum values, where the
    // first value gets assigned 0, and every subsequent value is 1 higher. 
    // Unfortunately, the resulting synthesis behavior is tool dependent.
    // Some versions of Quartus will not infer a state-machine for signed int
    // values:
    // https://www.intel.com/content/www/us/en/docs/programmable/683082/21-3/systemverilog-state-machine-coding-example.html
    //
    // Although the design will still work, it will be less efficient.
    // To work around this, there are several options.
    // For Quartus, you could use unsigned int values. The risk in using integers
    // is that the state register is now 32 bits. Quartus will optimize it to
    // whatever encoding you want, but other synthesis tools might not.
    // Uncomment the following to test different styles in your tool.

    /*typedef enum int unsigned {
                               STATE0,
                               STATE1,
                               STATE2,
                               STATE3 
                              } state_t;*/

    // Probably a safer alternative is to declare a logic array, like below.
    // Again, the potential risk in doing this is that a particular synthesis
    // tool might restrict the encoding to binary. Quartus does not, and
    // usually disregards the number of bits to use a 1-hot encoding, but other
    // tools may behave differently.
    //
    // MY RECOMMENDATION: To maximize portability across tools, start with the
    // logic array version and assume a binary encoding. If the FSM becomes a 
    // bottleneck, adjust the encoding to optimize for your specific tool.
    typedef enum logic [1:0] {
        STATE0,
        STATE1,
        STATE2,
        STATE3
    } state_t;

    // NOTE: I tried the following to avoid having to change the number of bits
    // when I add states and it crashed the version of Quartus I was using.
    //typedef enum logic [$clog2(STATE3+1)-1:0]  {

    // Declare a represent the state register (i.e. the current state). Notice
    // that its type is state_t.
    state_t state_r;

    // The 1-process FSM model treats the entire FSM like sequential logic in a
    // single process/block.   
    // In other words, all signals that are assigned values are implemented as
    // registers. Therefore, we will follow the exact same synthesis guidelines
    // as we did for sequential logic. 
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_r <= STATE0;
            out     <= 4'b0001;
        end else begin
            // Specify the output logic and next-state logic for each state.
            // This is as simple as translating each state from the fsm diagram.
            case (state_r)
                STATE0: begin
                    out <= 4'b0001;
                    // We don't need an else because state_r is already a register and
                    // will preserve the value automatically.
                    if (en) state_r <= STATE1;
                end
                STATE1: begin
                    out <= 4'b0010;
                    if (en) state_r <= STATE2;
                end
                STATE2: begin
                    out <= 4'b0100;
                    if (en) state_r <= STATE3;
                end
                STATE3: begin
                    out <= 4'b1000;
                    if (en) state_r <= STATE0;
                end
            endcase
        end
    end
endmodule  // moore_1p


// Module: moore_1p_2
// Description: This module is a slight modification of the previous module
// that illustrates how to encode states manually.

module moore_1p_2 (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [3:0] out
);
    // If we have a a good reason to choose our own state encoding, we can
    // do so manually assigning a value to each state. However, some tools
    // will not guarantee this encoding and may change it. In my tests on
    // Quartus, synthesis changed this encoding to a 1-hot encoding, despite
    // the explicit binary encoding. To avoid this, synthesis tools will have
    // flags that can specify the desired encoding:
    // https://www.intel.com/content/www/us/en/programmable/quartushelp/current/index.htm#hdl/vlog/vlog_file_dir_syn_encoding.htm
    //
    // SUGGESTION: Unless you have a very good reason to use a specific encoding,
    // don't use one. Omitting the encoding allows the synthesis tool to choose
    // one, which is likely going to be better for the targeted device.
    typedef enum logic [1:0] {
        STATE0 = 2'b00,
        STATE1 = 2'b01,
        STATE2 = 2'b10,
        STATE3 = 2'b11
    } state_t;

    state_t state_r;

    always_ff @(posedge clk, posedge rst) begin
        if (rst) begin
            state_r <= STATE0;
            out <= 4'b0001;
        end else begin
            case (state_r)
                STATE0: begin
                    out <= 4'b0001;
                    if (en) state_r <= STATE1;
                end
                STATE1: begin
                    out <= 4'b0010;
                    if (en) state_r <= STATE2;
                end
                STATE2: begin
                    out <= 4'b0100;
                    if (en) state_r <= STATE3;
                end
                STATE3: begin
                    out <= 4'b1000;
                    if (en) state_r <= STATE0;
                end
            endcase
        end
    end
endmodule


// Module: moore_2p
// Description: A 2-process/block model of the Moore FSM in fsm.pdf. In the
// 2-process model, we decompose the FSM into a state register (sequential 
// logic), and the next-state and output logic (combinational logic). Each type
// of logic uses a separate block and follows the synthesis guidelines for the
// corresponding type of logic.

module moore_2p (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [3:0] out
);

    typedef enum logic [1:0] {
        STATE0,
        STATE1,
        STATE2,
        STATE3
    } state_t;

    // For the 2-process model, we have a separate variable for the current
    // state (i.e. the state register), and the next state (i.e. the input to
    // the register to be stored on the next cycle).
    state_t state_r, next_state;

    // Create the state register. In this case, we use an abbreviated templated
    // because there will never be any other logic in this block. 
    always_ff @(posedge clk, posedge rst) begin
        if (rst) state_r <= STATE0;
        else state_r <= next_state;
    end

    // The next-state logic and output logic are purely combinational, so we
    // use an always_comb block, and follow synthesis guidelines accordingly.
    always_comb begin

        case (state_r)
            STATE0: begin
                out = 4'b0001;

                // Notice we are now assigning next_state instead of state_r because
                // state_r is the input to the combinational logic, whereas as
                // next_state is the output.
                if (en) next_state = STATE1;

                // For the 2-process model, we need the else statement (or some
                // alternative) because without it there would be a latch. If there
                // exists a path through a process/block for combinational logic
                // without a definition of a variable, that variable will be
                // synthesized as a latch.
                else
                    next_state = STATE0;
            end

            STATE1: begin
                out = 4'b0010;
                if (en) next_state = STATE2;
                else next_state = STATE1;
            end

            STATE2: begin
                out = 4'b0100;
                if (en) next_state = STATE3;
                else next_state = STATE2;
            end

            STATE3: begin
                out = 4'b1000;
                if (en) next_state = STATE0;
                else next_state = STATE3;
            end
        endcase
    end
endmodule


// Module: moore_2p_2
// Description: A slightly simpler 2-process alternative than the previous 
// implementation.

module moore_2p_2 (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [3:0] out
);

    typedef enum logic [1:0] {
        STATE0,
        STATE1,
        STATE2,
        STATE3
    } state_t;

    state_t state_r, next_state;

    always_ff @(posedge clk, posedge rst) begin
        if (rst) state_r <= STATE0;
        else state_r <= next_state;
    end

    always_comb begin
        // By assigning a default value to the next state, we eliminate the need
        // for all the else statements from the previous implementation. In
        // general, giving default values to combinational logic outputs will
        // prevent latches. There isn't always a natural default, but in this
        // case there is since the default applies to any time en = 0.
        next_state = state_r;

        case (state_r)
            STATE0: begin
                out = 4'b0001;
                if (en) next_state = STATE1;
            end

            STATE1: begin
                out = 4'b0010;
                if (en) next_state = STATE2;
            end

            STATE2: begin
                out = 4'b0100;
                if (en) next_state = STATE3;
            end

            STATE3: begin
                out = 4'b1000;
                if (en) next_state = STATE0;
            end
        endcase
    end
endmodule


// Module: moore
// Description: A top-level module for synthesis and simualtion. Change the
// name of the instantiated module to test different implementations.

module moore (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [3:0] out
);
    // IMPORTANT: Make sure to update the DELAY_CORRECT_OUTPUT parameter
    // in the testbench. It should be 1 for 1p and 0 for 2p.

    //moore_1p fsm (.*);
    //moore_1p_2 fsm (.*);
    //moore_2p fsm (.*);
    moore_2p_2 fsm (.*);

endmodule
