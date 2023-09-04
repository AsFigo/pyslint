class gen;

  randc bit [3:0] a,b; 
  bit [3:0] y;

  int min;
  int max;

  function void pre_randomize(input int min, input int max);
    this.min = min;
    this.max = max;  
  endfunction

  constraint data {
    a inside {[min:max]};
  b inside {[min:max]};
}

function void post_randomize();
  $display("Value of a :%0d and b: %0d", a,b);
endfunction
 endclass
