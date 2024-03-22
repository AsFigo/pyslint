class packet;
 rand bit [3:0] a[];
 
 constraint c1 { a.size == 10; }
 constraint c2 {
 foreach (a[i])
 // If 'i' is even or odd, set 'a[i]' to half of 'i'
 if (i % 2 == 0 || i % 2 == 1)
 a[i] == i / 2;
 }
endclass
module test;
 
 packet pkt = new;
 
 initial begin
 // Randomize the object 'pkt'
 pkt.randomize();
 
 // Display the values of array 'a' using '%p' format specifier
 $display("a = %p", pkt.a);
 end
endmodule