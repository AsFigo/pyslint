class ex_c;
  rand bit a,b,c;
  /*
 Let’s say that we have 3 single-bit variables a, b and c which have to be randomized so that c is 1 only if both a and b are 1. This could be a solution:
   */
  //however you might find some situations where you want to skip some values with in a certain range/ 
  constraint cst_wrong_oper_prec {
    a == b && c; }

  constraint cst_wrong_oper_prec_1 {
    a != b && c; }

  constraint cst_good_oper_prec {
    a == (b && c); }

  constraint cst_good_oper_prec_1 {
    a != (b && c); }

  constraint cst_or_wrong_oper_prec {
    a == b || c; }

  constraint cst_or_wrong_oper_prec_1 {
    a != b || c; }

  constraint cst_or_good_oper_prec {
    a == (b || c); }

  constraint cst_or_good_oper_prec_1 {
    a != (b || c); }

      /*
      But since equality operators have priority over logical operators, the expression in the constraint means “make sure that a is equal to c and that b is true” rather than “set c to be equal to a && b”. That is why b will be fixed to 1, which is potentially a problem since the cases when b is 0 never appear

      */
endclass : ex_c
