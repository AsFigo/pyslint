
//Even nos at odd positions and odd nos at even postions
class A;
  rand bit a[10];

  constraint c1 {
    foreach (a[i])
  {
            if(i%2==0)
                  a[i]%2 != 0 && a[i] != 0;
             else
                  a[i]%2 == 0 && a[i] != 0;
  }   
  }
endclass

module B;
    initial begin
         A h1 = new();
        h1.randomize();
        $display("a = %p",h1.a);
    end
endmodule 
