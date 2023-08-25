module empty_loop_p;

    initial
        begin
           for (int i = 0; i < 100; i++) begin
           $display("Not an empty loop");//loop is not empty
        end
        end
endmodule
