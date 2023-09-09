class c;
  rand bit [15 :0 ]x ;
  rand integer y;
  rand bit[1:0] z;

  constraint legal{
                      x>0;
                      z==3 -> x+1<=0;
                     if(z==2) {x+3<=0;}
                     z==0 -> {x+1>=0; x+2>=0;}
    }
 endclass
