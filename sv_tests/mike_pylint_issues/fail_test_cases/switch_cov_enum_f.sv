module switch_cov_enum_f;

   // Declare an enum data type
   enum { RED, GREEN, BLUE } color;

   // Declare a variable of the enum type
   color my_color;

   // Initialize the variable
   my_color = GREEN;

   // Use a switch statement to select the appropriate case
   switch (my_color) begin
      case RED:
         $display("The color is red.");
         break;
      case GREEN:
         $display("The color is green.");
         break;
      //case BLUE:
        // $display("The color is blue.");
        // break;
      default:
         $display("The color is unknown.");
         break;
   endcase

endmodule