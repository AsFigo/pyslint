`define AF_CIP_ERROR(ID, MSG) \
  `uvm_error (ID, MSG) 

interface axi3_m_cip #(
    parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 32
) (
  input wire aclk,
  input wire ARESETn,
  // Write Response Channel
  input wire [1:0] BRESP,
  input wire BVALID,
  output wire BREADY,
  // Write Data Channel
  input wire [DATA_WIDTH-1:0] WDATA,
  input wire [3:0] WSTRB,
  input wire WVALID,
  output wire WREADY,
  // Write Address Channel
  input wire [ADDR_WIDTH-1:0] AWADDR,
  input wire [AXI_ID_WIDTH-1:0] AWID,
  input wire [1:0] AWLEN,
  input wire [2:0] AWSIZE,
  input wire AWVALID,
  output wire AWREADY,
  // Read Data Channel
  output wire [DATA_WIDTH-1:0] RDATA,
  output wire [1:0] RRESP,
  output wire RVALID,
  input wire RREADY,
  // Read Address Channel
  input wire [ADDR_WIDTH-1:0] ARADDR,
  input wire [AXI_ID_WIDTH-1:0] ARID,
  input wire [7:0] ARLEN,
  input wire [2:0] ARSIZE,
  input wire ARVALID,
  output wire ARREADY
);
    

   string af_id = "AF";


 
  // Assert properties

  //========================================
  function void cip_fail_msg(string ID, MSG);
    `uvm_error (ID, MSG);
  endfunction : cip_fail_msg



  default clocking clock @(posedge aclk);
  endclocking
`ifndef VERILATOR
  default disable iff (!ARESETn);
`endif  // VERILATOR

  
  //==========================================

  /****  WRITE DATA CHANNEL ASSERTIONS   ****/

  //==========================================

  // property : WID remains stable when WVALID is asserted and WREADY is LOW.
  AXI_ERRM_WID_STABLE : assert property ( @(posedge aclk) 
                          ((WVALID && !WREADY) |-> ($stable(WID))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WID_STABLE", "WID is not stable when WVALID is asserted and WREADY is LOW ");

// property : A value of X on WID is not permitted when WVALID is HIGH.
  AXI_ERRM_WID_X : assert property ( @(posedge aclk) 
		     ((WVALID ===1'b1) |-> (WID !=='bX)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WID_X", "Value of X is on WID is permitted when WVALID is HIGH ");


// property : WDATA remains stable when WVALID is asserted and WREADY is LOW.
 AXI_ERRM_WDATA_STABLE: assert property ( @(posedge aclk) 
                          ((WVALID && !WREADY) |-> ($stable(WDATA))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WDATA_STABLE", "WDATA is unstable ");


// property : A value of X on WDATA is not permitted when WVALID is HIGH.
  AXI_ERRM_WDATA_X : assert property ( @(posedge aclk) 
		       ((WVALID ===1'b1) |-> (WDATA !=='bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WDATA_X", " Value of X is on WDATA is permitted when WVALID is HIGH ");


// property : WSTRB remains stable when WVALID is asserted and WREADY is LOW.
 AXI_ERRM_WSTRB_STABLE : assert property ( @(posedge aclk) 
                          ((WVALID && !WREADY) |-> ($stable(WSTRB))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WSTRB_STABLE", "WSTRB is not stable when WVALID is asserted and WREADY is LOW ");

// property : A value of X on WSTRB is not permitted when WVALID is HIGH
 AXI_ERRM_WSTRB_X : assert property ( @(posedge aclk) 
		      ((WVALID ===1'b1) |-> (WSTRB !== 'bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WSTRB_X", "A value of X on WSTRB is permitted");

// property : WLAST remains stable when WVALID is asserted and WREADY is LOW
 AXI_ERRM_WLAST_STABLE : assert property ( @(posedge aclk) 
                           ((WVALID && !WREADY) |-> ($stable(WLAST))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WLAST_STABLE", "WLAST is not stable");

// property : A value of X on WLAST is not permitted when WVALID is HIGH
 AXI_ERRM_WLAST_X : assert property ( @(posedge aclk) 
		      ((WVALID === 1'b1) |-> (WLAST !== 1'bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WLAST_X", "A value of X on WLAST is permitted");

// property : WVALID is LOW for the first cycle after ARESETn goes HIGH
 AXI_ERRM_WVALID_RESET : assert property ( @(posedge aclk) 
                           ((!$past(ARESETn) && ARESETn) |-> (!WVALID)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WVALID_RESET", "WVALID is not LOW for the first cycle after ARESETn");

// property : When WVALID is asserted then it must remain asserted until WREADY is HIGH
 AXI_ERRM_WVALID_STABLE : assert property ( @(posedge aclk) 
			    (WVALID |=> (WVALID && WREADY)));
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WVALID_STABLE", "When WVALID is not asserted");

// property : A value of X on WVALID is not permitted when not in reset
 AXI_ERRM_WVALID_X : assert property ( @(posedge aclk) 
		       ((!ARESETn) |-> (WVALID !== 1'bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WVALID_X", "Value of X on WVALID is permitted");

// property : A value of X on WREADY is not permitted when not in reset
 AXI_ERRS_WREADY_X : assert property ( @(posedge aclk) 
		       ((!ARESETn) |-> (WREADY !==1'bx )));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_WREADY_X", "A value of X on WREADY is permitted");

//================================================

  /****  WRITE ADDRESS CHANNEL ASSERTIONS   ****/

  //===============================================
   
  //The size of a write transfer does not exceed the width of the data interface
   check_AWSIZE: assert property (@(posedge aclk)
                   disable iff (!ARESETn) AWVALID && WVALID |-> (AWSIZE <= DATA_WIDTH));
         	     else 
			     `AF_CIP_ERROR("check_AWSIZE", "A value of X on AWSIZE is permitted");
     
   //AWID must remain stable when AWVALID is asserted and AWREADY is LOW 
    check_AWID_stable: assert property (@(posedge aclk)
					(AWVALID && !AWREADY)|-> ($stable(AWID));
                       else 
			 `AF_CIP_ERROR("check_AWID_stable", "AWID changes when AWVALID is asserted and AWREADY is LOW");
                                        

  //A value of X on AWID is not permitted when AWVALID is HIGH
   check_AWID_valid: assert property (@(posedge aclk) disable iff (!ARESETn)
    		       AWVALID |-> (AWID !== 'bx));
                     else 
		       `AF_CIP_ERROR("check_AWID_valid" ,"AWID has an invalid value when AWVALID is HIGH");

  //AXI_ERRM_AWADDR_BOUNDARY
   check_burst_boundary: assert property (@(posedge aclk) 
                            disable iff (AWREADY) ((AWADDR[11:0] + (AWLEN << AWIDTH)) < ((AWADDR[11:0] & 12'hFFF) + 12'h1000)));
                              else 
				`AF_CIP_ERROR("check_burst_boundary"," Write burst crosses a 4KB boundary");



  // Property statement:AWADDR remains stable when AWVALID is asserted and AWREADY is LOW
   check_AWADDR_stable: assert property @(posedge aclk)
	    (AWVALID && !AWREADY) |-> ($stable(AWADDR));
                        else 
	                  `AF_CIP_ERROR("check_AWADDR_stable","AWADDR is not stable");


  // A value of X on AWADDR is not permitted when AWVALID is HIGH
    check_AWADDR_not_permitted: assert property @(posedge aclk)
	                         (AWVALID) |-> (AWADDR !== 'bx));
                                else 
				  `AF_CIP_ERROR("check_AWADDR_not_permitted"," AWADDR is permitted");


  //A write transaction with burst type WRAP has a length of 2, 4, 8, or 16

   check_WRAP_length: assert property
                        (@(posedge aclk) disable iff (!ARESETn)
                        (AWVALID && (AWBURST == 2'b10)) |=> (AWLEN == 2'b01 ||
							      AWLEN == 2'b10 || 
							      AWLEN == 2'b11));
                      else 
			`AF_CIP_ERROR("check_WRAP_length","brust type WRAP length is not matching");

							

   //AWLEN remains stable when AWVALID is asserted and AWREADY is LOW
    check_AWLEN_stable: assert property (@(posedge aclk) 
					 ((AWVALID && !AWREADY) |-> ($stable(AWLEN))));
                        else 
		          `AF_CIP_ERROR("check_AWLEN_stable"," AWLEN is not stable");


    //A value of X on AWLEN is not permitted when AWVALID is HIGH

      check_AWLEN_Xnot_permitted: assert property (@(posedge aclk) 
                                    disable iff (!ARESETn) AWVALID |-> (AWLEN !== 'bx));
                                   else 
			             `AF_CIP_ERROR("check_AWLEN_Xnot_permitted"," AWLEN is permitted");


  //AWSIZE remains stable when AWVALID is asserted and AWREADY is LOW
   check_AWSIZE_stable: assert property (@(posedge aclk)
			((AWVALID && !AWREADY) |-> ($stable(AWSIZE))));
                        else 
		          `AF_CIP_ERROR("check_AWSIZE_stable"," AWSIZE is not stable");

 // property : AWBURST is not 2'b11 when AWVALID is HIGH
  AXI_ERRM_AWBURST: assert property ( @(posedge aclk) 
                          ( (AWVALID ) |-> (AWBURST != 2’b11));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_AWBURST", " AWBURST is not 2'b11 when AWVALID is HIGH");

 
// property : AWBURST remains stable when AWVALID is asserted and AWREADY is LOW
  AXI_ERRM_AWBURST_STABLE: assert property ( @(posedge aclk) 
                          ( (AWVALID && !AWREADY) |-> ($stable(AWBURST))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_AWBURST_STABLE ", " AWBURST remains stable when AWVALID is asserted and AWREADY is LOW ");
 
 
// property : AWBURST is not X when AWVALID is HIGH
  AXI_ERRM_AWBURST_X: assert property ( @(posedge aclk) 
                          (( AWVALID ) |-> (AWBURST !== 'bx))); 
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_AWBURST_X ", " AWBURST is not X when AWVALID is HIGH ");
 
// property : AWLOCK is not 2'b11 when AWVALID is HIGH
 AXI_ERRM_AWLOCK: assert property ( @(posedge aclk) 
                          ( (AWVALID) |-> (AWLOCK != 2’b11));                         
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_AWLOCK ", " AWLOCK is not 2'b11 when AWVALID is HIGH ");


	   
//============================================
 
 //***  WRITE RESPONSE CHANNEL ASSERTIONS ***//
 
 //============================================
 
 
 // property : BID remains stable when BVALID is asserted and BREADY is LOW.
  AXI_ERRS_BID_STABLE : assert property ( @(posedge aclk) 
                          ( (BVALID && !BREADY) |-> ($stable(BID))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_BID_STABLE", "BID is not stable when BVALID is asserted and BREADY is LOW ");

 
// property : A value of X on BID is not permitted when BVALID is HIGH
  AXI_ERRS_BID_X : assert property ( @(posedge aclk) 
                          ( (BVALID ) |-> (BID!=='bX)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_BID_X", "Value of X is on BID is permitted when BVALID is HIGH ");
 
 
// property : A value of X on BREADY is not permitted when not in reset
  AXI_ERRM_BREADY_X : assert property ( @(posedge aclk) 
                          (( !ARESETn) |-> (BREADY!=='bX))); 
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_BREADY_X", "A value of X on BREADY is not permitted when not in reset ");

 
// property : When BVALID is asserted then it must remain asserted until BREADY is HIGH
 AXI_ERRS_BVALID_STABLE : assert property ( @(posedge aclk) 
                          (BVALID && !BREADY) |=> (##[1:$] BVALID && BREADY));
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_BVALID_STABLE", "BVALID is asserted then it must remain asserted until BREADY is HIGH ");
 
 
// property : BRESP remains stable when BVALID is asserted and BREADY is LOW
 AXI_ERRS_BRESP_STABLE : assert property ( @(posedge aclk) 
                          ( (BVALID && !BREADY) |-> ($stable(BRESP))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_BRESP_STABLE", "BRESP remains stable when BVALID is asserted and BREADY is LOW ");


// property : A value of X on BRESP is not permitted when BVALID is HIGH
  AXI_ERRS_BRESP_X : assert property ( @(posedge aclk) 
                          ( (BVALID) |-> (BRESP!=='bX)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_BRESP_X", "A value of X on BRESP is not permitted when BVALID is HIGH ");
 
 
// property : BVALID is LOW for the first cycle after ARESETn goes HIGH
  AXI_ERRS_BVALID_RESET : assert property ( @(posedge aclk) 
		         ((ARESETn) |=> (!BVALID)));
                        else 
                           `AF_CIP_ERROR("AXI_ERRS_BVALID_RESET", "BVALID is LOW for the first cycle after ARESETn goes HIGH ");
	  
//==========================================

  /****  READ ADDRESS CHANNEL ASSERTIONS   ****/

  //==========================================

  // property : ARID remains stable when ARVALID is asserted and ARREADY is LOW
  AXI_ERRM_ARID_STABLE : assert property ( @(posedge aclk) 
                          ( (ARVALID && !ARREADY) |-> ($stable(ARID))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_WID_STABLE", "ARID is not stable when ARVALID is asserted and ARREADY is LOW ");

// property : A value of X on ARID is not permitted when ARVALID is HIGH
     AXI_ERRM_ARID_X : assert property ( @(posedge aclk)  
					((ARVALID) |-> (ARID!=='bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARID_X", "A value of X on ARID is permitted ");


 // property : ARADDR remains stable when ARVALID is asserted and ARREADY is LOW
  AXI_ERRM_ARADDR_STABLE : assert property ( @(posedge aclk) 
			     ((ARVALID && !ARREADY) |->$stable(ARADDR)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARADDR_STABLE", " ARADDR is not stable when ARVALID is asserted and ARREADY is LOW ");

 // property : A read transaction with a burst type of WRAP must have an aligned address
  AXI_ERRM_ARADDR_WRAP_ALIGN : assert property ( @(posedge aclk) disable iff (!ARVALID || ARREADY) 
				  (ARBURST == 3'b001 && (ARADDR !== 'bx)));  
                                else 
                                  `AF_CIP_ERROR("AXI_ERRM_ARADDR_WRAP_ALIGN", 
                                                                  " A read transcation with a burst type of WRAP not aligned address");

 // property : A value of X on ARADDR is not permitted when ARVALID is HIGH
   AXI_ERRM_ARADDR_X : assert property ( @(posedge aclk) disable iff (!ARVALID) 
                        (ARADDR!== 'bX));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARADDR_X", " A value of X on ARADDR is permitted when ARVALID is HIGH ");

// property : ARLEN remains stable when ARVALID is asserted and ARREADY is LOW
	  AXI_ERRM_ARLEN_STABLE : assert property ( @(posedge aclk) 
				    ((ARVALID && !ARREADY) |-> $stable(ARLEN)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARLEN_STABLE", " ARLEN remains unstable when ARVALID is asserted and ARREADY is LOW ");

// property : A value of X on ARLEN is not permitted when ARVALID is HIGH
   AXI_ERRM_ARLEN_X: assert property ( @(posedge aclk) disable iff (!ARVALID) 
		       (ARLEN !==8'bX));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARLEN_X", "  A value of X on ARLEN is  permitted when ARVALID is HIGH ");

// property : ARSIZE remains stable when ARVALID is asserted and ARREADY is LOW
	  AXI_ERRM_ARSIZE_STABLE: assert property ( @(posedge aclk) 
				    ((ARVALID && !ARREADY) |-> $stable(ARSIZE)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARSIZE_STABLE", 
                                                      " ARSIZE remains unstable when ARVALID is asserted and ARREADY is LOW ");

// property : A value of X on ARSIZE is not permitted when ARVALID is HIGH
   AXI_ERRM_ARSIZE_X: assert property ( @(posedge aclk) disable iff (!ARVALID) 
                          (ARSIZE !=='bX));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARSIZE_X", " A value of X on ARSIZE is permitted when ARVALID is HIGH ");

// property : A value of 2'b11 on ARBURST is not permitted when ARVALID is HIGH
   AXI_ERRM_ARBURST: assert property ( @(posedge aclk) disable iff (!ARVALID) 
                          (ARBURST !== 4'b11));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARBURST", " A value of 2'b11 on ARBURST is permitted when ARVALID is HIGH ");

// property : ARBURST remains stable when ARVALID is asserted and ARREADY is LOW
  AXI_ERRM_ARBURST_STABLE: assert property ( @(posedge aclk) 
			     ((ARVALID && !ARREADY) |-> $stable(ARBURST)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARBURST_STABLE", " ARBURST remains unstable when ARVALID is asserted and ARREADY is LOW ");

// property : A value of X on ARBURST is not permitted when ARVALID is HIGH
   AXI_ERRM_ARBURST_X: assert property ( @(posedge aclk) disable iff (!ARVALID) 
                         (ARBURST !=='bX));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARBURST_X", " A value of X on ARBURST is permitted when ARVALID is HIGH ");

// property : ARBURST remains stable when ARVALID is asserted and ARREADY is LOW
 AXI_ERRM_ARBURST_STABLE: assert property ( @(posedge aclk) 
			    ((ARVALID && !ARREADY) |-> $stable(ARBURST)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_ARBURST_STABLE", " ARBURST remains unstable when ARVALID is asserted and ARREADY is LOW ");

//============================================
 
 //***** READ DATA CHANNEL ASSERTIONS *****//
 
 //============================================

// property : RID remains stable when RVALID is asserted and RREADY is LOW
  AXI_ERRS_RID_STABLE : assert property ( @(posedge aclk) 
                          ( (RVALID && !RREADY) |-> ($stable(RID)))); 
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RID_STABLE", "RID remains stable when RVALID is asserted and RREADY is LOW ");
 
 
// property : A value of X on RID is not permitted when RVALID is HIGH
  AXI_ERRS_RID_X : assert property ( @(posedge aclk) 
				    ( (RVALID) |-> (RID!=='bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RID_X", "A value of X on RID is not permitted when RVALID is HIGH ");
 
 
// property : RVALID is LOW for the first cycle after ARESETn goes HIGH.
  AXI_ERRS_RVALID_reset: assert property ( @(posedge aclk) 
                         ((ARESETn) |=> (!RVALID)));
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RDATA_NUM", "The number of read data items must match the corresponding ARLEN");

 
// property : RDATA remains stable when RVALID is asserted and RREADY is LOW.
  AXI_ERRS_RDATA_STABLE : assert property ( @(posedge aclk) 
                          ( (RVALID && !RREADY) |-> ($stable(RDATA))))
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RDATA_STABLE", "RDATA remains stable when RVALID is asserted and RREADY is LOW");
 
 
// property : RRESP remains stable when RVALID is asserted and RREADY is LOW
  AXI_ERRS_RRESP_STABLE : assert property ( @(posedge aclk) 
                          ( (RVALID && !RREADY) |-> ($stable(RRESP))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RRESP_STABLE", "RRESP remains stable when RVALID is asserted and RREADY is LOW ");

 
// property : A value of X on RRESP is not permitted when RVALID is HIGH
  AXI_ERRS_RRES_X : assert property ( @(posedge aclk) 
		         ( (RVALID ) |-> (RRESP!=='bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RRES_X", "A value of X on RRESP is not permitted when RVALID is HIGH ");

 
// property : RLAST remains stable when RVALID is asserted and RREADY is LOW
  AXI_ERRS_LAST_STABLE : assert property ( @(posedge aclk) 
                          ( (RVALID && !RREADY) |-> ($stable(RLAST))));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_LAST_STABLE", "RLAST remains stable when RVALID is asserted and RREADY is LOW ");
 
 
// property : A value of X on RLAST is not permitted when RVALID is HIGH 
  AXI_ERRS_RLAST_X : assert property ( @(posedge aclk) 
		         ( (RVALID) |-> (RLAST!=='bx)));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RLAST_X", "A value of X on RLAST is not permitted when RVALID is HIGH  ");


// property : RVALID is LOW for the first cycle after ARESETn goes HIGH.
 AXI_ERRS_RVALID_RESET: assert property ( @(posedge aclk) 
                          ( (ARESETn) |=> ( !RVALID )));  
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RVALID_RESET" RVALID is LOW for the first cycle after ARESETn goes HIGH ");

 
// property : When RVALID is asserted then it must remain asserted until RREADY is HIGH.
  AXI_ERRS_RVALID_STABLE: assert property ( @(posedge aclk) 
		         ( ( RVALID) |=> (RVALID throughout (!RREADY))));
                        else 
                          `AF_CIP_ERROR("AXI_ERRS_RVALID_STABLE", " When RVALID is asserted then it must remain asserted until RREADY is HIGH.
");
 
 
// property : A value of X on RVALID is not permitted when not in reset.
  AXI_ERRS_RVALID_X: assert property ( @(posedge aclk) 
                          ((ARESETn) |-> RVALID != 1’bx)));
                        else 
                           `AF_CIP_ERROR("AXI_ERRS_RVALID_X", " A value of X on RVALID is not permitted when not in reset ");



// property : A value of X on RREADY is not permitted when not in reset.
  AXI_ERRM_RREADY_X: assert property ( @(posedge aclk)                      
                         ((ARESETn) |-> RREADY != 1’bx)));
                        else 
                          `AF_CIP_ERROR("AXI_ERRM_RREADY_X", " A value of X on RREADY is not permitted when not in reset. ");

	  
 initial begin : init
    `g2u_display("Using CIP");
  end : init
endinterface : axi_m_cip
