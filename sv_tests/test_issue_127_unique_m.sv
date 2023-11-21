

module case_test; 
logic  ack1, ack2, req1, req2, bus_switch, b;
logic[1:0] bus_select;
bit clk;
initial forever #10 clk=!clk; 
default clocking cb_clk @ (posedge clk); endclocking
    property p; @ (posedge clk) b; endproperty : p
	    ap_active_bus : assert property(
		    disable iff (bus_switch)
		    if (bus_select) p

			    else  p); 

			    initial begin
				    clk = 0;
				    ack1 = 0;
				    ack2 = 0;
				    req1 = 0;
				    req2 = 0;
				    ##1; bus_switch = 0;
				    b = 0;
				    bus_select = 2'b00;
				    bus_switch = 1;
				    ##100; $finish;
			    end

			    endmodule : case_test

			    module unique_m;
			    bit[3:0] a; 
			    bit clk, b; 
			    initial forever #10 clk=!clk; 
			    always_ff @ (posedge clk)  begin : aly 
				    unique if ((a==0) || (a==1)) $display("a=%d a, should be 0 or 1", a);
				    else if (a == 2) $display("a=%d a, should be 2", a);
				    else if (a == 4) $display("a=%d a, should be 4", a); // values 3,5,6,7 cause a violation report
				    priority if (a[2:1]==0) $display("a=%d a, priority should be0 or 1", a);
				    else if (a[2] == 0) $display("a=%d a, priority should be 2 or 3", a);
				    else $display("a=%d a, priority should be 4 to 7", a); // covers all 
			    end  : aly

		    always @(negedge clk) begin
			    a <= a+1'b1; 

		    end

		    property p; @ (posedge clk) b; endproperty : p

			    caseassert2 : assert property(p);

			    property foo; @ (posedge clk)
				    case (a)
					    1:  b;
					    2:  p;
					    default:  p;
				    endcase
			    endproperty

			    caseassert : assert property(foo);


			    initial begin
				    clk = 0;
				    b = 0;
				    a = 0;
				    b=1;
				    #10;
				    a = 2;
				    #10;
				    #10 $finish;
			    end


			    endmodule : unique_m


