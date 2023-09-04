typedef enum bit [2:0] {
    STATE_A = 3'b000,
    STATE_B = 3'b001,
    STATE_C = 3'b010,
    STATE_D = 3'b011
} StateType;

module enum_setmembership_ops_f;
    StateType current_state;

    initial begin
        current_state = STATE_B;

        // Failure test case
        if (current_state inside {STATE_A, STATE_D}) // Attempting to use unsupported enum values

                $display("Current state is either STATE_A or STATE_D");
        else
                $display("Current state is not STATE_A or STATE_D");

    end
endmodule