module switch_issue_f;
   typedef enum int { A, B, C, D, E, F, G, H} packet_type_t;
   packet_type_t pkt_type;

   initial begin
           pkt_type = A;
      //void'(randomize(pkt_type));
      case (pkt_type) inside
        A,D :  $write("case 1 ");
        B,C :  $write("case 2 ");
        //[E:G] :  $write("case 3 ");//All case items are not covered
        //default : $write("default ");
      endcase // case (pkt_type)
      $display(pkt_type.name);
   end
endmodule
