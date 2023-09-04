class generator;
   randc bit [3:0] a, b; //rand or randc 
   bit [3:0] y;
   /*
   constraint data_a {a > 3; a < 7;}
   constraint data_b {b == 3;}
   */
   //constraint data {a > 3; a < 7 ; b > 0;}
    /*
   Here if we want to apply randomization in some specific ranges 
   constraint data {
     a inside {[0:8],[10:11],15} ; //0 1 2 3 4 5 6 7 8  10 11 15  
     b inside {[3:11]} ;  // 3 4 5 6 7 8 9 10 11  
          }
   */
   //however you might find some situations where you want to skip some values with in a certain range/ 
   constraint data {
     !(a inside {[3:7]});
     !(b inside {[5:9]});
      }
   // a = 3:7, b = 5:9
 endclass
