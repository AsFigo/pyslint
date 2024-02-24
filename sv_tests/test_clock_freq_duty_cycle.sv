module test;
 
 logic clk = 0;
 
 property p1(int tolerance, realtime half_duty_cycle);
 realtime current_time;
 // At every positive edge of the clock, capture the current time
 @(posedge clk) (1, current_time = $realtime) |->
 // At the next negative edge, check if the high period is within the 
specified tolerance
 @(negedge clk) ($realtime - current_time) >= half_duty_cycle -
(half_duty_cycle * tolerance) / 100.0 &&
 ($realtime - current_time) <= half_duty_cycle +
(half_duty_cycle * tolerance) / 100.0;
 endproperty : p1
 property p2(int tolerance, realtime half_duty_cycle);
 realtime current_time;
 // At every negative edge of the clock, capture the current time
 @(negedge clk) (1, current_time = $time) |->
 // At the next positive edge, check if the low period is within the 
specified tolerance
 @(posedge clk) ($realtime - current_time) >= half_duty_cycle -
(half_duty_cycle * tolerance) / 100.0 &&
 ($realtime - current_time) <= half_duty_cycle +
(half_duty_cycle * tolerance) / 100.0;
 endproperty : p2
 // Assert the high period of the clock with a tolerance of 5% and a halfduty cycle of 50ns
 clk_high: assert property (p1(5, 50ns));
 // Assert the low period of the clock with the same tolerance and half-duty 
cycle
 clk_low: assert property (p2(5, 50ns));
 
 // Clock generation block
 always begin
 clk = 1'b1; // Set clock high
 #20; // Wait for 20 time units
 clk = 1'b0; // Set clock low
 #80; // Wait for 80 time units, creating a 100ns clock period with a 
20/80 duty cycle
 end
 
 initial begin
 #2000 $finish;
 end
 
 // Setup for dumping waveforms to a .vcd file for analysis
 initial begin 
 $dumpfile("dump.vcd");
 $dumpvars;
 end 
 
endmodule