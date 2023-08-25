typedef enum bit [2:0] {
    STATE_A = 3'b000,
    STATE_B = 3'b001,
    STATE_C = 3'b010,
    STATE_D = 3'b011
} StateType;

module enum_setmembership_ops_p;
    StateType current_state;

    initial begin
        current_state = STATE_B;
        // Successful set membership operation
        if (current_state inside {STATE_A, STATE_B, STATE_C})
        //set membership operations to check if a given value belongs to the enum's defined set
            $display("Current state is either STATE_A, STATE_B, or STATE_C");
        else
            $display("Current state is not STATE_A, STATE_B, or STATE_C");

    end
endmodule