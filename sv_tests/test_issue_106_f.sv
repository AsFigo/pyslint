   module fifo ( clk, reset_n, empty,almost_empty,almost_full, full,data_out,error,data_in,push,pop);
         timeunit 1ns;  timeprecision 100ps;  
         parameter BIT_DEPTH = 4; // 2**BIT_DEPTH = depth of fifo 
         parameter FULL = 15;    // int'(2** BIT_DEPTH -1);
         parameter ALMOST_FULL = 10; // int'(3*FULL / 4);
         parameter ALMOST_EMPTY = 4;  //int'(FULL/4);
         parameter WIDTH = 32;
         typedef logic [WIDTH-1 : 0] word_t;
         typedef word_t [0 : (2**BIT_DEPTH-1)] buffer_t;

         input clk;
         input reset_n;
         output empty;
         output almost_empty;
         output almost_full;
         output full;
         output word_t data_out;
         output error;
         input word_t data_in;
         input push;
         input pop;
        // =====
        logic [BIT_DEPTH-1 : 0] wr_addr; // write fifo address
        logic [BIT_DEPTH-1 : 0] rd_addr; // read fifo address  
        buffer_t buffer; // fifo storage
        parameter shiftVal = int'(2**BIT_DEPTH) ;

        // Push on full with no pop error 
        property p_push_error; 
                @ (posedge clk) 
                 not (push && full && !pop); 
        endproperty : p_push_error
        ap_push_error_1 : assert property (p_push_error);
  
          property p_pop_error; 
              @ (posedge clk) 
              not (pop && empty); 
         endproperty : p_pop_error
        ap_pop_error_1 : assert property (p_pop_error);

       // RTL Detailed design
        logic [1:0]            push_pop;
      // Defining control for maintenance of FIFO word count
       assign     push_pop = {push , pop};    // temporary concatenation 
     // providing READ data to output
      assign data_out = buffer[rd_addr]; 
 
       always @ (posedge clk or negedge reset_n) 
          begin 
             if (!reset_n)  
                 begin  // asynchronous reset (active low)
                       rd_addr         <= 0;
                       wr_addr         <= 0;
                 end
           else
             begin
               case (push_pop)
                 2'b00 :
                       ;              // no push, no pop
            
                2'b01 : 
                   begin                   // no push, pop for READ 
                     rd_addr         <= (rd_addr+1) % shiftVal;
                    end   
                2'b10 :                    // push for WRITE, no pop
                  begin              
                     wr_addr         <= (wr_addr + 1) % shiftVal;
                     buffer[wr_addr] <= data_in;
                  end
               2'b11 :                    // push for WRITE, pop for READ
                 begin
                    rd_addr <= (rd_addr+1) % shiftVal;
                    wr_addr <= (wr_addr + 1) % shiftVal;
                    buffer[wr_addr] <= data_in;
               end
             default  :
               begin
  /*             a_illegal_fifo_cmd_1 : assert (1'b0) else
                 $warning ("%0t %0m Meta value detected in FIFO command, push_pop %2b ",
                           $time, push_pop);
 */
//		a_illegal_fifo_cmd_1 : assert property (1'b0) ;
             end
           
             endcase
          end //else
      end //always

        assign  error = (pop && empty) || (push && full && !pop);
        assign full = (wr_addr - rd_addr) == FULL;
       assign empty = (wr_addr == rd_addr);
       assign almost_full = (wr_addr - rd_addr) >= ALMOST_FULL;
       assign almost_empty = (wr_addr - rd_addr) <= ALMOST_EMPTY;
  
 endmodule : fifo
          
module tb_fifo;

  reg clk;
  reg reset_n;
  wire empty;
  wire almost_empty;
  wire almost_full;
  wire full;
  wire [31:0] data_out;
  wire error;
  reg [31:0] data_in;
  reg push;
  reg pop;

  // Instantiate the FIFO module
  fifo dut (
    .clk(clk),
    .reset_n(reset_n),
    .empty(empty),
    .almost_empty(almost_empty),
    .almost_full(almost_full),
    .full(full),
    .data_out(data_out),
    .error(error),
    .data_in(data_in),
    .push(push),
    .pop(pop)
  );

  // Provide clock signal
  always begin
    #5 clk = ~clk; // Example clock period of 10 time units
  end

 

  // Test stimulus
  initial begin
    clk = 0;
    reset_n = 0;
    data_in = 0;
    push = 0;
    pop = 0;
 
   
    #10 reset_n = 1;
    data_in = 32'h12345678;
    #10;
    pop = 1;
    #10;
    push = 1;
    data_in = 32'hABCDEF01;
    
    $finish; 
  end
endmodule