
 class distribution;
   
   // actually if we are not using ranges of values there is no diff between (:=) and (:/) operators
   rand bit sel;// :=
   rand bit en;// :/
   
   // but if we use ranges of values there we can recognize the diff
   
   rand bit [0:3] data1;//:=
   rand bit [0:3] data2;//:/
   
   constraint one{
     sel dist {0:=10, 1:=90};
     en dist {0:/10, 1:/90};
     data1 dist {0:=10, [1:3]:=60};
     data2 dist {0:/10, [1:3]:/60};
   }
   
 endclass
   
 module tb();
   
   distribution d;
   
   initial begin
     d = new();
     
     for(int i = 0; i < 10; i++) begin
       if(d.randomize()) begin 
       end else begin
         $display("randomization failed");
       end
     #10 
       $display("sel = %0d, en = %0d ", d.sel, d.en);
       $display("data1 = %0d, data2 = %0d ", d.data1, d.data2);
       
     end
   end
   
 endmodule
