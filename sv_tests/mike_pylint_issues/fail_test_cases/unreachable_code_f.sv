module unreachable_code_f;

initial
begin
        if (1'b0) begin
            $display("The code is not reachable");// Unreachable code
        end else begin
          $display("The code is reachable"); // Reachable code
        end
end
endmodule