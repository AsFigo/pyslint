       `include "uvm_macros.svh"
        import uvm_pkg::*;

       module chkr_c_test#(mn=0, mx=20);
          bit clk = 0;
          reg a = 0;
          reg b = 0;
          reg d = 0;
          reg [31:0] min = 0;
          reg [31:0] max = 0;
          logic x, y; 
          assign x = a;  

       initial forever #5 clk = ~clk;
                ap_ok_in_module: assert property(@ (posedge clk)
                a |-> ##[mn:mx] b); 

       always_ff @ (posedge clk) begin 
                automatic int k; 
                k= max; 
                if(b) ap_xy: assert property(x |=> y[*2:10]);
                ap_max: assert property(k <10 |-> ##[1:10] y);
       end
              
      initial begin
  
               clk = 0;
               a = 0;
               b = 0;
               d = 0;
               min = 0;
               max = 20;
               #10 a = 1;
               #10 b = 1;
               #10 d = 1;
               #10 min = 5;
               #10 $finish;
      end
              
   endmodule: chkr_c_test
              
   `include "uvm_macros.svh"

        checker c1(event clk, logic[7:0] a, b);
                logic [7:0] sum;
                initial forever #5 clk = ~clk;

     `define MAX_SUM 100
               always_ff @(clk) begin
               sum <= a + 1'b1;
               p0: assert property (sum < `MAX_SUM);
    end
 
             p1: assert property (@clk sum < `MAX_SUM);
             p2: assert property (@clk a != b);
             p3: assert #0 ($onehot(a));
    endchecker

    checker c_top (event clk, logic[7:0] a, b, logic d);
              if(d) 
              c1 c1_i(posedge clk, a, b); 
     endchecker : c_top

     checker c_top_equivalent (event clk, logic[7:0] a, b, logic d);
             logic [7:0] sum;
             always_ff @(clk) begin
              sum <= a + 1'b1;
              p0: assert property (sum < `MAX_SUM);
      end

            if(d) begin :if1
            p1: assert property (@clk sum < `MAX_SUM);
            p2: assert property (@clk a != b);
            p3: assert #0 ($onehot(a));
      end : if1
              
          initial begin
               clk = 0;

     end

         initial begin    
              a = 8'h00;
              b = 8'h01;
              d = 0;

            #10 a = a + 1'b1;
            #10 b = b + 1'b1;
            #20 d = 1;
            #30 d = 0;

            #100 $finish;
     end
              
   endchecker : c_top_equivalent


 module m_top;
        logic clk, cond1, cond2; 
        logic[7:0] a, b;
        always @ (posedge clk) 
        if(cond1) @(posedge clk, a, b, cond2); 
  endmodule : m_top

 module m_top_equivalent;
        logic cond1;
        bit clk;
        logic [7:0] a, b;
        logic [7:0] sum;

        initial forever #5 clk = ~clk;

    always @(posedge clk) begin
           sum <= a + 1'b1;
            p0: assert property (sum < `MAX_SUM);
            if (cond1) begin
            p1: assert property (@(posedge clk) sum < `MAX_SUM);
            p2: assert property (@(posedge clk) a !== b); // Using !== for inequality
            p3: assert property (@(posedge clk) $onehot(a));
        end
    end
              
       initial begin
           cond1 = 0;
           clk = 0;
           a = 8'h00;
           b = 8'h01; 

          #10 cond1 = 1;
          #10 a = a + 1'b1;
          #10 b = b + 1'b1;
    
          #1000 $finish;
    end    
             
    endmodule : m_top_equivalent




  module top_legal;
         bit clk;
//      initial forever #10 clk=!clk; 
         default clocking cb_clk @ (posedge clk);  endclocking 
         int svar1 = 1; // static keyword optional
   initial begin
            for (int i=0; i<3; i++) begin
            automatic int loop3 = 0; // executes every loop
            for (int j=0; j<3; j++) begin
            loop3++;
            $display(loop3);
            end
        end 
            for (int i=0; i<3; i++) begin
            static int loop2 = 0; // executes once before time 0
            for (int j=0; j<3; j++) begin
            loop2++;
            $display(loop2);
            end
        end 
    end
  endmodule : top_legal

  module top_illegal; // should not compile
       initial begin
             static int svar2 = 2; // static/automatic needed to show intent
             for (int i=0; i<3; i++) begin
             static int loop3 = 0; // illegal statement
            for (int i=0; i<3; i++) begin
             loop3++;
             $display(loop3);
            end
        end
    end
  endmodule : top_illegal

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    class class_ex; 
       rand int addr;
       task main();
            a_BAD_STYLE: assert (randomize(addr))
            else $fatal(1, "Randomization of var failed: conflicting constraints"
             );
            a_GOOD_STYLE: if(!randomize(addr))  `uvm_error("run_phase", "seq randomization failure"
            ); 
     endtask : main
  endclass : class_ex 

  module counter; 
        timeunit 1ns; 
        timeprecision 100ps;
        logic clk=0, reset_n=0, go = 0, sop;
        int cntr =0, pkt_data, pkt_len, addr;
        bit  CFG_NO_JUMBO_PKTS;

    always @(posedge clk) begin  : aly1
            if (sop && pkt_data == 'h8000)   
            if (CFG_NO_JUMBO_PKTS) 
            a_plklen : assert (pkt_len < 9576) else
                $error ("detected a jumbo pkt while current configuration prevents that"
                );  
    end : aly1

        property pCounterMaxed;
                @ (posedge clk) disable iff (!reset_n)
                go |=> (cntr <= 3);
        endproperty : pCounterMaxed

        apCounterMaxed : assert property (pCounterMaxed) else 
            $fatal(0, "%0t SVA_ERR: Counter exceeded 3, cntr %0d; sampled(cntr) %0d ",
            $time, cntr, $sampled(cntr));

        default clocking @(negedge clk); endclocking
            initial  
               begin : clk_gen
               clk <= 0;  forever #5 clk <= ~clk;
        end

        initial
        begin : stim
            @ (negedge clk); 
             reset_n = 1;
             go = 1;
             repeat (10) @ (negedge clk);

            $finish; 
        end 
       
   endmodule : counter

