module signedness_f;

logic [7:0] reqA;

initial begin
        reqA = -4;//reqA can store unsigned value not signed value-signedness issue
        $display("value of reqA:%0b",reqA);
end
endmodule