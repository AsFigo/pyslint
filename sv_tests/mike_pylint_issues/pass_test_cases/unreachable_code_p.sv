module unreachable_code_p;

initial
begin
        if (1'b1) begin
            $display("The code is reachable");// Reachable code
        end else begin
          $display("The code is not reachable"); // unreachable code
        end
end
endmodule