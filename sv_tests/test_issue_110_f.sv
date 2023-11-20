
    module memory_data_integrity_check ();
        logic write; // memory write
        logic read;  // memory read
        logic  wdata; // data written to memory
        logic  rdata; // data read from memory
        logic  addr;  // memory address 
        bit reset_n; // active low reset
        bit clk;

        timeunit 1ns;
        timeprecision 100ps;
        int mem_aarray[*]; // associative array to be used by property
        wire mem_aaray_exists;  // exists at specified address
        initial forever #10 clk=!clk; 
        default clocking cb_clk @ (posedge clk);  endclocking 
        assign mem_aarray_exists = mem_aarray.exists(addr); 

        always@ (posedge clk)
	    if (reset_n==1'b0) mem_aarray.delete; // Clears AA elements
	    else if (write) mem_aarray[addr] = wdata; // store data


         property p_read_after_write;
		  @(posedge clk)
		  (read && mem_aarray_exists) |-> mem_aarray[addr]==rdata; 
	 endproperty : p_read_after_write
	 ap_read_after_write : assert property (p_read_after_write);

	 property p_read_before_write;
		  @(posedge clk)
		  not (read && !mem_aarray_exists);
	 endproperty : p_read_before_write
	 ap_read_before_write : assert property (p_read_before_write);

            initial begin

		  // Apply reset
		  reset_n = 0;
		  reset_n = 1;


		  addr = 4'h0; 
		  read = 1;   
		  write = 0;  
		  wdata = 32'hA5A5A5A5;

		  read = 0;

		  addr = 4'h1;
		  write = 1;
		  wdata = 32'h12345678;
		  ##10; $finish;
	    end

	  endmodule : memory_data_integrity_check
