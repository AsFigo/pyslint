module signedness_p;

logic [7:0] reqA;

initial begin
        reqA =$unsigned(8'b11111100);//reqA can store unsigned value not signed value(-4->11111100) so casting to unsigned
        $display("value of reqA:%0b",reqA);
end
endmodule