module test;
 // Clock period defined in nanoseconds
 time clk_period = 10.0 / 1.0ns;
 
 // Define a clock signal
 bit clk;
 
 // Clock generation: toggle clk every 5 ns to get a 10ns period (100 MHz 
frequency)
 always #5 clk = ~clk;
 
 // Define a property to check the clock frequency
 property p1(int clk_period);
 realtime current_time;
 // Check if the clock period matches the expected value
 // Capture the current time at the rising edge of the clock
 // and ensure the difference between two rising edges matches clk_period
 (('1, current_time = $realtime) |=> (clk_period == $realtime -
current_time));
 endproperty
 // Assert the clock frequency at every positive edge of the clock
 clk_frequency: assert property (@(posedge clk) p1(clk_period))
 // If the assertion passes, display a message
 $display("%m :: Time = [%0t]ns clk frequency is correct, Assertion 
Pass", $realtime);
 else
 // If the assertion fails, display an error message
 $error("%m :: Time = [%0t] clk not correct, Assertion fail", $realtime);
 
 // Main test sequence
 initial begin 
 // Check the clock signal for a number of cycles
 for(int i = 0; i < 20; i++)
 @(posedge clk);
 // Finish simulation
 $finish;
 end
 
 // Initialize simulation dump for waveform analysis
 initial begin 
 $dumpfile("dump.vcd");
 $dumpvars;
 end
endmodule
