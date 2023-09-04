module MultiBitPosedge_p(input logic [7:0] signal);
    logic [7:0] prev_signal;
    always @(posedge signal) begin
        for (int i = 0; i < 8; i++) begin
            if (signal[i] && !prev_signal[i]) begin
                // Rising edge detected on bit i
                $display("Posedge detected on bit %0d of signal.", i);
            end
        end
        prev_signal <= signal;
    end
endmodule