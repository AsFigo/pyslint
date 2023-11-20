
    module memory_data_integrity_check (); 
       bit write; // memory write
       bit read;  // memory read
       bit[31:0] wdata; // data written to memory
       bit[31:0]  addr;  // memory address -- small for simulation 
       bit reset_n; // active low reset
       bit clk;
       timeunit 1ns;   timeprecision 100ps;
       initial forever #5 clk=!clk;
       default clocking cb_clk @ (posedge clk);  endclocking 
       int mem_aarray[*];
       bit [31:0] rdata;  
       bit  mem_aarray_exists;  
       assign mem_aarray_exists  = mem_aarray.exists(addr); 
       always_comb 
         if(mem_aarray_exists) 
            rdata  = mem_aarray[addr];   
       always@ (posedge clk)
         if (reset_n==1'b0) mem_aarray.delete; 
         else if (write) mem_aarray[addr]  = wdata; 
       property p_read_after_write;
         bit [31:0] v_wrdata, v_wraddr;
         (write, v_wraddr=addr, v_wrdata= wdata) |-> 
          (read && mem_aarray_exists && addr==v_wraddr) [->1] |-> 
          rdata==v_wrdata;  
       endproperty : p_read_after_write
       ap_read_after_write : assert property (p_read_after_write)
        $info("addr =%h, rdata=%h", $sampled(addr), $sampled(rdata)); else 
        $error("addr =%h, rdata=%h", $sampled(addr), $sampled(rdata)); 
        
       property p_read_before_write;
        not (read && !mem_aarray_exists); 
       endproperty : p_read_before_write
       ap_read_before_write : assert property (p_read_before_write);
      
        initial begin
            reset_n = 0;
            write = 0;
            read = 0;
            wdata = 0;
            addr = 0;
            // Release reset after some time
            #20 reset_n = 1;
            // Write data to memory
            #30 write = 1;
            #40  wdata = 32'h12345678;
            #50 addr = 32'h00000001;
            #60 write = 0;
            // Read data from memory
           #70 read = 1;
           #80 addr = 32'h00000001;
           #10 $finish;
        end
    
  endmodule : memory_data_integrity_check

  class c_xactn;
     rand bit write; 
     rand bit read; 
     rand int wdata; 
     and bit[31:0] addr; 
     constraint addr_range_cst { addr <= 15 ;}
     constraint no_wr_and_rd_cst { !(read && write);}
    endclass : c_xactn
   module top;
      timeunit 1ns;   timeprecision 100ps;
      bit write; // memory write
      bit read;  // memory read
      int wdata; // data written to memory
      int rdata; // data read from memory
      bit[31:0] addr;  // memory address 
      bit reset_n=1'b1; // active low reset
      bit clk=1'b1;   // clock
      c_xactn c1=new(); 
      memory_data_integrity_check mem_check1 (.*);   
 endmodule : top 
