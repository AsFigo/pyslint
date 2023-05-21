class bug_c;
  rand bit num_list[32];
  rand int a;

  constraint cst_sum { 
    num_list.sum() == 1; 
    num_list.and() == 1; 
    num_list.xor() == 1; 
    num_list.product() == 1; 
    //num_list.sum() with (6'(item)) == 1; 
    //a > 1;
  }
endclass : bug_c

