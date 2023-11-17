    module d29(); 
    timeunit 1ns;
    timeprecision 100ps;

    logic bus_enb,bus_ack,done,dma_ack,mem_enb,bus_req,dma_req;
    bit clk;

    initial forever #10 clk=!clk; 
    default clocking cb_clk @ (posedge clk);  endclocking  

    sequence qBusTransfer; 
	@ (posedge clk) ##[1:5] bus_ack ##1 bus_enb [*1:128] ##1 done;
    endsequence : qBusTransfer
    d29assert : assert property (qBusTransfer);

    sequence qDmaTransfer; 
	@ (posedge clk) ##[1:3] dma_ack ##1 mem_enb[*128]; 
    endsequence :  qDmaTransfer
    d29assert1 : assert property (qDmaTransfer);

    property BusXfr_XOR_DmaXfr; 
	@ (posedge clk)  not ($rose(bus_req) or $rose(dma_req)); 
    endproperty : BusXfr_XOR_DmaXfr
    d29assert2 : assert property (BusXfr_XOR_DmaXfr);

    property IfBusXfr_NoDmaXfr; 
	@ (posedge clk)    $rose(bus_req) and !$rose(dma_req)
	|-> !qDmaTransfer.ended throughout qBusTransfer; 
    endproperty : IfBusXfr_NoDmaXfr
    d29assert3 : assert property (IfBusXfr_NoDmaXfr);

    property IfDmaXfr_NoBusXfr; 
	@ (posedge clk)    $rose(dma_req) and !$rose(bus_req) 
	|-> !qBusTransfer.ended throughout qDmaTransfer; 
    endproperty : IfDmaXfr_NoBusXfr
    d29assert4 : assert property (IfDmaXfr_NoBusXfr);

        initial begin
	    dma_ack = 1;
	    mem_enb = 1;
	    dma_ack = 0;
	    #10 mem_enb = 0;
	    bus_req = 1;
	    dma_req = 1;
	    ##1; bus_req = 0;
	    ##5; dma_req = 0;

	    ##5;$finish;
        end
    endmodule :d29