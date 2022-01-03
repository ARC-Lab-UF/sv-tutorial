module fib
  (
   input logic 	     clk,
   input logic 	     rst,
   input logic 	     go,
   input logic [4:0] n,   
   output logic [31:0] result,
   output logic done
   );

   typedef enum {START, COND, COMPUTE, DONE, RESTART} state_t;
   state_t state_r;   

   logic [$bits(n)-1:0] n_r, i_r;
   logic [$bits(result)-1:0] x_r, y_r;   
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 state_r <= START;
	 result <= '0;
	 done <= 1'b0;
	 
	 i_r <= '0;
	 x_r <= '0;
	 y_r <= '0;
	 n_r <= '0;	
      end
      else begin
       
	 case (state_r)
	   START : begin
	      done <= 1'b0;
	      result = '0;
	      
	      n_r = n;
	      i_r = 3;	   
	      x_r = '0;
	      y_r = 1;	   
	      
	      if (go == 1'b1)
		state_r <= COND;	      
	   end
	   
	   COND : begin
	      if (i_r <= n_r)
		state_r = COMPUTE;
	      else
		state_r = DONE;	   
	   end
	   
	   COMPUTE : begin	      
	      x_r <= y_r;	      
	      y_r <= x_r + y_r;
	      i_r ++;
	      state_r <= COND;	      
	   end

	   DONE : begin
	      if (n_r < 2)
		result <= x_r;
	      else
		result <= y_r;
	      
	      done <= 1'b1;
	      if (go == 1'b0)
		state_r <= RESTART;	      	     
	   end

	   RESTART : begin
	      n_r = n;
	      i_r = 3;	   
	      x_r = '0;
	      y_r = 1;
	      
	      if (go == 1'b1) begin
		 done <= 1'b0;
		 state_r <= COND;		 
	      end
	   end
	 endcase      
      end
   end   
endmodule

/* module fib
  (
   input logic 	     clk,
   input logic 	     rst,
   input logic 	     go,
   input logic [4:0] n,   
   output logic [31:0] result,
   output logic done
   );

   typedef enum {START, COND, COMPUTE, FINISHED, RESTART} state_t;
   state_t state_r, next_state;   
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 state_r <= STATE;
	 result_r <= '0;	 
      end
      else begin
	 state_r <= next_state;	
      end
   end

   always_comb begin

      next_state = state_r;
      next_n = n_r;      
      
      case (state_r)
	START : begin
	   if (go == 1'b1)
	      next_state = INIT;

	   done = 1'b0;
	   
	   next_n = n;
	   next_i = 3;	   
	   next_x = 0;
	   next_y = 1;	   
	   next_result = '0;
	end

	COND : begin
	   if (x <= n_r)
	     next_state = COMPUTE;
	   else
	     next_sate = COMPLETE;	   
	end

	COMPUTE : begin
	   temp = x + y;
	   x = y;
	   y = temp;
	   i ++;	   	   
	end
	
      endcase
      
   end
   
endmodule
*/
