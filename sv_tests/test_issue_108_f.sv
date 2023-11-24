  
   module bus_xfr_data_integrity_check ;
     logic wr_33 = 0;
     logic rd_25 = 0;
     logic [31:0] wdata = 0;
     logic [31:0] rdata = 0;
     logic reset_n = 1;
     bit clk_xt33 = 0;
     bit clk_rcv25 = 0;
     bit clk;
     timeunit 1ns;   timeprecision 100ps;
     parameter MAX_BUFF_SIZE=1024; 
     logic[31:0] waddr;  // write address for storage of incoming data
     logic[31:0] raddr;  // read address for reading of received data
     logic[31:0] rdata_from_q; // read data from queue to compare to Receiver
     logic[31:0] dataQ [$]; // queue, to store/read incoming data
     /*logic[31:0]*/ int dataQsize; // queue size. 
    //assign dataQsize= dataQ.size; //CVC change commented 
    default clocking cb_clk @ (posedge clk_rcv25);  endclocking 
    // Storage of data into queue
  	initial forever #10 clk_rcv25 = ~clk_rcv25;
     initial forever #10 clk_xt33 = ~clk_xt33;
    always  @ (posedge clk_xt33)
    if (reset_n==1'b0)
      dataQ = {}; // clear the queue contents
    else begin if (wr_33) dataQ.push_front(wdata);  // store data
 	dataQsize = dataQ.size;//CVC change added current line
	end
    // Collect data from the Q 
    always  @ (posedge clk_rcv25)
      if (rd_25)  rdata_from_q <= dataQ.pop_back();

     // Data integrity check 
    property p_read_data_integrity; 
    @(posedge clk_rcv25)
      rd_25 |=>  rdata_from_q==rdata;
    endproperty : p_read_data_integrity
    ap_read_data_integrity : assert property (p_read_data_integrity);

    // Never a READ with no data received
    property p_never_read_on_empty;
     @(posedge clk_rcv25)
      not (dataQsize == 0 && rd_25);
    endproperty : p_never_read_on_empty
    ap_never_read_on_empty : assert property (p_never_read_on_empty);

    // never a write on a full buffer 
    property p_never_write_on_max_buff;
     @(posedge clk_xt33)
      not (dataQsize == MAX_BUFF_SIZE && wr_33);
      endproperty : p_never_write_on_max_buff
    ap_write_on_max_buff : assert property (p_never_write_on_max_buff);
   
    initial begin
      
       ##10; rdata <= 32'b1100_0011_1010_0101_1111_0000_1111_1010;
       rdata_from_q<=32'b1100_0011_1010_0101_1111_0000_1111_1010;
       rd_25 <= 1;
       ##10;$finish;
    end

 endmodule : bus_xfr_data_integrity_check
