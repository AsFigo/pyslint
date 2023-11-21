module local_var;
bit clk, req, ack, done, crc_pass, crc_err, busy=1, ready=0, reset, x, a=0,  
	b0, b, c, d, x1=1, x0=0;
bit a1=1, a2=1, a0, a4, a5, reset_n; 
int i=4, j=8, k=4; 
default clocking cb_clk @ (posedge clk);
    endclocking 
    default disable iff  (reset);
    initial forever #10 clk=!clk;
    property P; 
	    int v=0; 
	    a1 |->
		    (a2, v=v+1)[*0:1] ##1 v==j; 
    endproperty : P

    property P_init; 
	    int v=0; 
	    a1 |->   
		    (a2, v=v+1)[*0:1] ##1 v==j; 
    endproperty : P_init
    ap_P: assert property(P_init);


    function automatic int f(int x, y);     
	    return x==y; 
    endfunction : f
    property P3_OK; 
	    int v; 
	    (a1, v=0) |-> 
		    (f(i, k)[*1:2], v=v+1)[*0:1] ##1 v==15; 
    endproperty : P3_OK
    ap_P3: assert property(P3_OK);

    property P3_Illegal;
	    int v = 0;
	    (a1, v=0) |-> (f(i, k), v=v+1) ##1 v==15;
    endproperty : P3_Illegal
    ap_Illegal: assert property(P3_Illegal);

    property P4; 
	    int v; 
	    (a1, v=0)|-> (a[*1:2], v=v+1)[*1:2] ##1 v==5; 
    endproperty : P4
    ap_P4: assert property(P4);

    property P5; 
	    int v=0; 
	    (a1, v=0) |-> a[*0:2] ##1 v==5;       
    endproperty : P5
    ap_P5: assert property(P5);

    initial begin

	    reset = 1;
	    reset = 0;
	    a <= 1'b0; 
	    a1<=1;
	    a2<=1;
	    a <= 1'b1;
	    a <= 1'b0;
	    ##10; $finish;
    end

    endmodule : local_var
