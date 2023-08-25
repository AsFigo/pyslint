module MultiBitPosedge_f(input logic [7:0] signal);
//whenever there is a transition from 0 to 1 enter the always block
    always @(posedge signal) begin
        // Your code here
		
        $display("Posedge detected on any bit of signal.");
    end
endmodule