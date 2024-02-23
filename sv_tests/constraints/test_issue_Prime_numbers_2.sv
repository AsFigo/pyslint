class packet;

 rand bit[7:0] a[$], b[$];

 // Define a constraint 'c1' to ensure that the size of array 'a' is exactly
200 elements
 constraint c1 { a.size == 200; }

 // Define a constraint 'c2' to populate array 'a' with prime numbers
 constraint c2 {
 foreach (a[i])
 if (i > 1)
 // Constrain 'a[i]' to be a prime number using the 'prime_num'
function
 a[i] == prime_num(i);
 }

 // Function to check if a number is prime
 function int prime_num(int c);
 for (int i = 2; i < c; i++)
 if (c % i == 0)
 return 2; // Return 2 if the number is not prime (2 is a placeholder
indicating not prime)
 // If the loop completes without finding a divisor, 'c' is a prime number
 prime_num = c;
 endfunction

 // Function to be executed after randomization
 function void post_randomize();
 // Remove duplicate elements from array 'a'
 a = a.unique;

 // Iterate over the elements of 'a'
 for (int i = 0; i < a.size(); i++)
 // Check if the unit place of 'a[i]' is 7
 if (a[i] % 10 == 7)
 // If the unit place is 7, add 'a[i]' to array 'b'
 b.push_back(a[i]);
 endfunction
endclass
module test;

 packet pkt = new;

 initial begin
 void'(pkt.randomize());
 // Display the randomized values of array 'a' and 'b' using '%p' format
specifier
 $display("%p", pkt);
 end
endmodule
