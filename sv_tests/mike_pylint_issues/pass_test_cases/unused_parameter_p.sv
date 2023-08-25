module unused_parameter_p #(parameter DATA_WIDTH = 8, ID_WIDTH = 32) (data, id);
  //Used the parameters declared as DATA_WIDTH and ID_WIDTH
  input bit [DATA_WIDTH-1: 0] data;
  input bit [ID_WIDTH-1: 0] id;

  initial begin
    // Display width values
    $display("DATA_WIDTH = %0d, ID_WIDTH = %0d", DATA_WIDTH, ID_WIDTH);

    // Display variables
    $display("data = %0d,  id = %0d", data, id);
  end
endmodule