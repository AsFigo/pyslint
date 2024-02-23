class packet;

 rand bit [3:0] a[];

 constraint c1 { a.size == 21; }

 constraint c2 {
 foreach (a[i])
 // If 'i' is even or odd, set 'a[i]' to one-third of 'i'
 if (i % 2 == 0 || i % 2 == 1)
 a[i] == i / 3;
 }
endclass
module test;

 packet pkt = new;

 initial begin
 pkt.randomize();

 // Display the values of array 'a' using '%p' format specifier
 $display("a = %p", pkt.a);
 end
endmodule
