module unused_parameter_f #(parameter DATA_WIDTH = 8, ID_WIDTH = 32) (data, id);
//unused parameter ,parameter DATA_WIDTH is not used anywhere
  input bit [ID_WIDTH-1: 0] data;
  input bit [ID_WIDTH-1: 0] id;

  initial begin
    // Display width values
    $display("DATA_WIDTH = %0d, ID_WIDTH = %0d", DATA_WIDTH, ID_WIDTH);

    // Display variables
    $display("data = %0d,  id = %0d", data, id);
  end
endmodule