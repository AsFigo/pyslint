module machine(input wire clk);

  typedef enum logic [1:0] {S0, S1, S2} state_t;

  state_t state;

endmodule

