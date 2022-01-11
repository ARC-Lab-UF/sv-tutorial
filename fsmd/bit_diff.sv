module bit_diff_fsmd_1p
  #(
    parameter WIDTH
    )
   (
    input logic 				clk,
    input logic 				rst,
    input logic 				go,
    input logic [WIDTH-1:0] 			data,
    output logic signed [$clog2(2*WIDTH+1)-1:0] result,
    output logic 				done    
    );

   typedef enum 				{START, COMPUTE, RESTART} state_t;
   state_t state_r;

   logic [$bits(data)-1:0] 			data_r;
   logic [$bits(result)-1:0] 			result_r;
   logic [$clog2(WIDTH)-1:0] 			count_r;
   logic signed [$clog2(2*WIDTH+1)-1:0] 	diff_r;
   logic 					done_r;

   // These concurrent assignments aren't necessary, but they preserve the 
   // naming convention of having all registers use a _r suffix without 
   // requiring the outputs to have the suffix. I prefer to not name the
   // outputs based on the internal representation for several reasons. First,
   // there may be parameters for a module that change whether or not the
   // output is registered, which could make the suffix misleading. Second,
   // the user of the module usually doesn't need to know if an output is
   // registered. They might need to know the timing, but that can be specified
   // in documentation, which is more meaningful than just knowing the 
   // existence of a register. Finally, retiming might move all the registers
   // anyway, in which case there might not be a register on the output.
   //
   // For simple modules, this convention is overkill, but becomes useful when
   // using large modules because every variable that appears on the LHS of
   // an assignment within an always_ff should have a _r suffix. If you
   // accidentally assign a signal that isn't intended to be a register, then
   // the naming convention helps catch that mistake.
   assign result = result_r;
   assign done = done_r;

   // In the 1-process FSMD, everything is captured in a single always block.
   // It doesn't have to be an always_ff block in case there is combinational
   // logic mixed into the assignments, but use the always_ff when possible.
   always_ff @(posedge clk or posedge rst) begin
      if (rst == 1'b1) begin	 
	 
	 result_r <= '0;
	 done_r <= 1'b0;	 	 
	 diff_r <= '0;	 
	 count_r <= '0;
	 data_r <= '0;	 
	 state_r <= START;	 
      end
      else begin

	 done_r <= 1'b0;
	 
	 case (state_r)
	   START : begin

	      // Assign outputs.
	      done_r <= 1'b0;
	      result_r <= '0;
	      
	      // Initialize internal state.
	      diff_r <= '0;
	      count_r <= '0;
	      data_r <= data;

	      // Wait for go to be asserted.
	      if (go == 1'b1) state_r <= COMPUTE;	       
	   end

	   COMPUTE : begin

	      // Add one to the difference if asserted, else subtract one.
	      diff_r <= data_r[0] == 1'b1 ? diff_r + 1 : diff_r - 1;	  

	      // Shift out the current lowest bit.
	      data_r <= data_r >> 1;
	      count_r <= count_r + 1;

	      // We are done after checking WIDTH bits. The -1 is used because
	      // the count_r assignment is non-blocking. When subtracting from
	      // a variable, this would create an addition subtractor, which
	      // we definitely want to avoid. However, in this case, WIDTH
	      // is a parameter, which is treated as a constant. Synthesis will
	      // do constant propagation and replace WIDTH-1 with a constant,
	      // so this will just be a comparator.
	      //
	      // We could also use a blocking assignment in the previous
	      // statement and then get rid of the -1, but since this is an
	      // always_ff block, it could introduce linter warnings.
	      if (count_r == WIDTH-1) state_r <= RESTART; 
	   end

	   // This state could easily be combined with START, but was done
	   // this way on purpose to match the FSM+D version, where done is
	   // not registered.
	   RESTART : begin
	      // Assign outputs.
	      result_r <= diff_r;
	      done_r <= 1'b1;

	      // Reset internal state.
	      diff_r <= '0;
	      count_r <= '0;
	      data_r <= data;
	      
	      if (go == 1'b1) begin
		 // If we don't clear done here, then we'll get an assertion
		 // error because it will take an extra cycle for done to be
		 // cleared after the circuit is restarted.
		 done_r <= 1'b0;		 
		 state_r <= COMPUTE;
	      end
	   end
	 endcase	  
      end      
   end   
endmodule


module bit_diff_fsmd_2p
  #(
    parameter WIDTH
    )
   (
    input logic 				clk,
    input logic 				rst,
    input logic 				go,
    input logic [WIDTH-1:0] 			data,
    output logic signed [$clog2(2*WIDTH+1)-1:0] result,
    output logic 				done    
    );

   typedef enum 				{START, COMPUTE, RESTART} state_t;

   // For a 2-process FSMD, every register needs a variable for the output of
   // the register, which is the current value represented by the _r suffix,
   // and a variable for the input to the register (i.e., the next value), which
   // is determined by combinational logic.
   state_t state_r, next_state;
   logic [$bits(data)-1:0] 			data_r, next_data;
   logic [$bits(result)-1:0] 			result_r, next_result;
   logic [$clog2(WIDTH)-1:0] 			count_r, next_count;
   logic signed [$clog2(2*WIDTH+1)-1:0] 	diff_r, next_diff;

   assign result = result_r;
      
   // The first process simply implements all the registers.
   always_ff @(posedge clk or posedge rst) begin
      if (rst == 1'b1) begin
	 result_r <= '0;
	 diff_r <= '0;	 
	 count_r <= '0;
	 data_r <= '0;	 
	 state_r <= START;	 
      end
      else begin
	 result_r <= next_result;
	 diff_r <= next_diff;
	 count_r <= next_count;
	 data_r <= next_data;
	 state_r <= next_state;
      end 
   end 

   // The second process implements any combinational logic, which includes
   // the inputs to all the registers, and any other combinational logic. For
   // example, in this module the done output is not registered like in the
   // the 1-process model. Although the 2-process model seems like overkill for
   // this example, the advantage is that you can control exactly what is
   // registered. For complex designs, registering everything is usually not
   // ideal, which makes the 2-process model version.
   always_comb begin

      logic [$bits(diff_r)-1:0] diff_temp;
            
      // Since this is combinational logic, we should never be assigning a
      // _r version of the signals. The left hand side should either be a next_
      // signal, or other variables that correspond to combinational logic.
      //
      // Here we assign default values to all the register inputs to make sure
      // we don't have latches. For a register, a good default value is usually
      // the current value because then we only have to assign the signal later
      // if the register is going to change.
      next_result = result_r;
      next_diff = diff_r;
      next_data = data_r;
      next_count = count_r;
      next_state = state_r;

      // Done is combinational logic in this module, so it doesn't have a 
      // "next" version. 
      done = 1'b0;
            
      case (state_r)	
	START : begin
	   done <= 1'b0;
	   next_result = '0;	   
	   next_diff <= '0;
	   next_data <= data;
	   next_count <= '0;

	   // Without the default assignment at the beginning of the block,
	   // this would result in a latch.
	   if (go == 1'b1) next_state <= COMPUTE;	       
	end
	
	COMPUTE : begin	
	   //done <= 1'b0;   
	   //next_diff = data_r[0] == 1'b1 ? diff_r + 1 : diff_r - 1;
	   diff_temp = data_r[0] == 1'b1 ? diff_r + 1 : diff_r - 1;
	   next_diff = diff_temp;	   
	   next_data = data_r >> 1;
	   next_count = count_r + 1;

	   // Here, we could compare with next_count also and get rid of the
	   // -1. However, that would be non-ideal for two reasons. First,
	   // The addition for the count becomes an input to the comparator
	   // without a register in between, which could increase the the
	   // length of the critical path and slow down the clock. Second,
	   // the count variable would need an extra bit for the new condition
	   // to ever be true, which would increase the size of the adder, the
	   // comparator, and the register. 
	   if (count_r == WIDTH-1) begin
	      next_state = RESTART;

	      // For us to be able to assert done in the next cycle, we need
	      // to send it to the result register this cycle. Also, we need
	      // to use the next version of diff since the register won't be
	      // updated yet.
	      next_result = diff_temp;
	   end
	end

	// The restart state is now identical to the start state with the
	// exception of the done signal, which is now asserted. Basically, the
	// logic for done has been moved from a separate register into the
	// state register.
	RESTART : begin	  
	   done <= 1'b1;	   	   
	   next_diff <= '0;
	   next_count <= '0;
	   next_data <= data;

	   // Since done is now combinational logic, we don't want to clear it
	   // here otherwise it will be cleared in the same cycle that go
	   // is asserted. If that is desired behavior, it is fine to do so,
	   // but the specification for this module requires done to be cleared
	   // one cycle after the assertion of go.
	   //
	   // One reason to avoid clearing done within the same cycle as go is
	   // that the logic for go outside this module could depend on done,
	   // then creates a combinational loop. The 1-cycle delay avoids this
	   // problem.
	   if (go == 1'b1) next_state = COMPUTE;
	end
      endcase	  
   end      
endmodule
