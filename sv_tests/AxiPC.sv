//============================================================================--
//  This confidential and proprietary software may be used only as
//  authorised by a licensing agreement from ARM Limited
//    (C) COPYRIGHT 2003-2009 ARM Limited
//        ALL RIGHTS RESERVED
//  The entire notice above must be reproduced on all authorised
//  copies and copies may only be made to the extent permitted
//  by a licensing agreement from ARM Limited.
//
//
//------------------------------------------------------------------------------
//  Version and Release Control Information:
//
//  File Name           : AxiPC.sv,v
//  File Revision       : 66202
//
//  Release Information : BP062-VL-70004-r0p1-00rel0
//
//------------------------------------------------------------------------------
//  Purpose             : This is the AXI Protocol Checker using SVA
//
//                        Supports bus widths of 32, 64, 128, 256, 512, 1024 bit
//                        Parameterisable write interleave depth
//                        Supports a single outstanding exclusive read per ID
//============================================================================--

//----------------------------------------------------------------------------
// CONTENTS
// ========
//  299.  Module: AxiPC
//  366.    1) Parameters
//  370.         - Configurable (user can set)
//  424.         - Calculated (user should not override)
//  497.    2) Inputs (no outputs)
//  501.         - Global Signals
//  507.         - Write Address Channel
//  522.         - Write Data Channel
//  533.         - Write Response Channel
//  542.         - Read Address Channel
//  557.         - Read Data Channel
//  567.         - Low Power Interface
//  575.    3) Wire and Reg Declarations
//  722.    4) Verilog Defines
//  726.         - Lock FSM States
//  735.         - Clock and Reset
//  768.    5) Initialize simulation
//  773.         - Format for time reporting
//  779.         - Indicate version and release state of AxiPC
//  784.         - Warn if any/some recommended rules are disabled
//  804.         - Warn if any/some channel rules are ignored
//  820. 
//  821.  AXI Rules: Write Address Channel (*_AW*)
//  826.    1) Functional Rules
//  830.         - AXI_ERRM_AWADDR_BOUNDARY
//  854.         - AXI_ERRM_AWADDR_WRAP_ALIGN
//  866.         - AXI_ERRM_AWBURST
//  878.         - AXI_ERRM_AWCACHE
//  890.         - AXI_ERRM_AWLEN_WRAP
//  905.         - AXI_ERRM_AWLOCK
//  917.         - AXI_ERRM_AWLOCK_END
//  931.         - AXI_ERRM_AWLOCK_ID
//  954.         - AXI_ERRM_AWLOCK_LAST
//  970.         - AXI_ERRM_AWLOCK_START
//  986.         - AXI_ERRM_AWSIZE
// 1000.         - AXI_ERRM_AWVALID_RESET
// 1012.         - AXI_RECM_AWLOCK_BOUNDARY
// 1037.         - AXI_RECM_AWLOCK_CTRL 
// 1061.         - AXI_RECM_AWLOCK_NUM
// 1084.    2) Handshake Rules
// 1088.         - AXI_ERRM_AWADDR_STABLE
// 1101.         - AXI_ERRM_AWBURST_STABLE
// 1114.         - AXI_ERRM_AWCACHE_STABLE
// 1127.         - AXI_ERRM_AWID_STABLE
// 1140.         - AXI_ERRM_AWLEN_STABLE
// 1153.         - AXI_ERRM_AWLOCK_STABLE
// 1166.         - AXI_ERRM_AWPROT_STABLE
// 1179.         - AXI_ERRM_AWSIZE_STABLE
// 1192.         - AXI_ERRM_AWVALID_STABLE
// 1204.         - AXI_RECS_AWREADY_MAX_WAIT
// 1220.    3) X-Propagation Rules
// 1226.         - AXI_ERRM_AWADDR_X
// 1237.         - AXI_ERRM_AWBURST_X
// 1248.         - AXI_ERRM_AWCACHE_X
// 1259.         - AXI_ERRM_AWID_X
// 1270.         - AXI_ERRM_AWLEN_X
// 1281.         - AXI_ERRM_AWLOCK_X
// 1292.         - AXI_ERRM_AWPROT_X
// 1303.         - AXI_ERRM_AWSIZE_X
// 1314.         - AXI_ERRM_AWVALID_X
// 1325.         - AXI_ERRS_AWREADY_X
// 1339. 
// 1340.  AXI Rules: Write Data Channel (*_W*)
// 1345.    1) Functional Rules
// 1349.         - AXI_ERRM_WDATA_NUM
// 1364.         - AXI_ERRM_WDATA_ORDER
// 1375.         - AXI_ERRM_WDEPTH
// 1387.         - AXI_ERRM_WSTRB
// 1398.         - AXI_ERRM_WVALID_RESET
// 1411.    2) Handshake Rules
// 1415.         - AXI_ERRM_WDATA_STABLE
// 1428.         - AXI_ERRM_WID_STABLE
// 1441.         - AXI_ERRM_WLAST_STABLE
// 1454.         - AXI_ERRM_WSTRB_STABLE
// 1467.         - AXI_ERRM_WVALID_STABLE
// 1479.         - AXI_RECS_WREADY_MAX_WAIT 
// 1495.    3) X-Propagation Rules
// 1501.         - AXI_ERRM_WDATA_X
// 1512.         - AXI_ERRM_WID_X
// 1523.         - AXI_ERRM_WLAST_X
// 1534.         - AXI_ERRM_WSTRB_X
// 1545.         - AXI_ERRM_WVALID_X
// 1556.         - AXI_ERRS_WREADY_X
// 1570. 
// 1571.  AXI Rules: Write Response Channel (*_B*)
// 1576.    1) Functional Rules
// 1580.         - AXI_ERRS_BRESP
// 1591.         - AXI_ERRS_BRESP_ALL_DONE_EOS
// 1608.         - AXI_ERRS_BRESP_EXOKAY
// 1619.         - AXI_ERRS_BVALID_RESET
// 1631.         - AXI_RECS_BRESP 
// 1644.    2) Handshake Rules
// 1648.         - AXI_ERRS_BID_STABLE
// 1661.         - AXI_ERRS_BRESP_STABLE
// 1674.         - AXI_ERRS_BVALID_STABLE
// 1686.         - AXI_RECM_BREADY_MAX_WAIT 
// 1702.    3) X-Propagation Rules
// 1708.         - AXI_ERRM_BREADY_X
// 1719.         - AXI_ERRS_BID_X
// 1730.         - AXI_ERRS_BRESP_X
// 1741.         - AXI_ERRS_BVALID_X
// 1755. 
// 1756.  AXI Rules: Read Address Channel (*_AR*)
// 1761.    1) Functional Rules
// 1765.         - AXI_ERRM_ARADDR_BOUNDARY
// 1789.         - AXI_ERRM_ARADDR_WRAP_ALIGN
// 1801.         - AXI_ERRM_ARBURST
// 1813.         - AXI_ERRM_ARCACHE
// 1825.         - AXI_ERRM_ARLEN_WRAP
// 1840.         - AXI_ERRM_ARLOCK
// 1852.         - AXI_ERRM_ARLOCK_END
// 1866.         - AXI_ERRM_ARLOCK_ID
// 1889.         - AXI_ERRM_ARLOCK_LAST
// 1904.         - AXI_ERRM_ARLOCK_START
// 1920.         - AXI_ERRM_ARSIZE
// 1932.         - AXI_ERRM_ARVALID_RESET
// 1944.         - AXI_RECM_ARLOCK_BOUNDARY
// 1969.         - AXI_RECM_ARLOCK_CTRL
// 1993.         - AXI_RECM_ARLOCK_NUM
// 2016.    2) Handshake Rules
// 2020.         - AXI_ERRM_ARADDR_STABLE
// 2033.         - AXI_ERRM_ARBURST_STABLE
// 2046.         - AXI_ERRM_ARCACHE_STABLE
// 2059.         - AXI_ERRM_ARID_STABLE
// 2072.         - AXI_ERRM_ARLEN_STABLE
// 2085.         - AXI_ERRM_ARLOCK_STABLE
// 2098.         - AXI_ERRM_ARPROT_STABLE
// 2111.         - AXI_ERRM_ARSIZE_STABLE
// 2124.         - AXI_ERRM_ARVALID_STABLE
// 2136.         - AXI_RECS_ARREADY_MAX_WAIT 
// 2152.    3) X-Propagation Rules
// 2158.         - AXI_ERRM_ARADDR_X
// 2169.         - AXI_ERRM_ARBURST_X
// 2180.         - AXI_ERRM_ARCACHE_X
// 2191.         - AXI_ERRM_ARID_X
// 2202.         - AXI_ERRM_ARLEN_X
// 2213.         - AXI_ERRM_ARLOCK_X
// 2224.         - AXI_ERRM_ARPROT_X
// 2235.         - AXI_ERRM_ARSIZE_X
// 2246.         - AXI_ERRM_ARVALID_X
// 2257.         - AXI_ERRS_ARREADY_X
// 2271. 
// 2272.  AXI Rules: Read Data Channel (*_R*)
// 2277.    1) Functional Rules
// 2281.         - AXI_ERRS_RDATA_NUM
// 2295.         - AXI_ERRS_RLAST_ALL_DONE_EOS
// 2312.         - AXI_ERRS_RID
// 2325.         - AXI_ERRS_RRESP_EXOKAY
// 2337.         - AXI_ERRS_RVALID_RESET
// 2350.    2) Handshake Rules
// 2354.         - AXI_ERRS_RDATA_STABLE
// 2369.         - AXI_ERRS_RID_STABLE
// 2382.         - AXI_ERRS_RLAST_STABLE
// 2395.         - AXI_ERRS_RRESP_STABLE
// 2408.         - AXI_ERRS_RVALID_STABLE
// 2420.         - AXI_RECM_RREADY_MAX_WAIT 
// 2436.    3) X-Propagation Rules
// 2442.         - AXI_ERRS_RDATA_X
// 2453.         - AXI_ERRM_RREADY_X
// 2464.         - AXI_ERRS_RID_X
// 2475.         - AXI_ERRS_RLAST_X
// 2486.         - AXI_ERRS_RRESP_X
// 2497.         - AXI_ERRS_RVALID_X
// 2511. 
// 2512.  AXI Rules: Low Power Interface (*_C*)
// 2517.    1) Functional Rules (none for Low Power signals)
// 2522.    2) Handshake Rules (asynchronous to ACLK)
// 2529.         - AXI_ERRL_CSYSACK_FALL
// 2540.         - AXI_ERRL_CSYSACK_RISE
// 2551.         - AXI_ERRL_CSYSREQ_FALL
// 2562.         - AXI_ERRL_CSYSREQ_RISE
// 2574.    3) X-Propagation Rules
// 2580.         - AXI_ERRL_CACTIVE_X
// 2591.         - AXI_ERRL_CSYSACK_X
// 2602.         - AXI_ERRL_CSYSREQ_X
// 2616. 
// 2617.  AXI Rules: Exclusive Access
// 2625.    1) Functional Rules
// 2627.         -
// 2630.         - AXI_ERRM_EXCL_ALIGN
// 2651.         - AXI_ERRM_EXCL_LEN
// 2669.         - AXI_RECM_EXCL_MATCH
// 2692.         - AXI_ERRM_EXCL_MAX
// 2713.         - AXI_RECM_EXCL_PAIR
// 2730. 
// 2731.  AXI Rules: USER_* Rules (extension to AXI)
// 2739.    1) Functional Rules (none for USER signals)
// 2744.    2) Handshake Rules
// 2748.         - AXI_ERRM_AWUSER_STABLE
// 2761.         - AXI_ERRM_WUSER_STABLE
// 2774.         - AXI_ERRS_BUSER_STABLE
// 2787.         - AXI_ERRM_ARUSER_STABLE
// 2800.         - AXI_ERRS_RUSER_STABLE
// 2814.    3) X-Propagation Rules
// 2820.         - AXI_ERRM_AWUSER_X
// 2831.         - AXI_ERRM_WUSER_X
// 2842.         - AXI_ERRS_BUSER_X
// 2853.         - AXI_ERRM_ARUSER_X
// 2864.         - AXI_ERRS_RUSER_X
// 2878. 
// 2879.  Auxiliary Logic
// 2884.    1) Rules for Auxiliary Logic
// 2889.       a) Master (AUXM*)
// 2893.         - AXI_AUXM_DATA_WIDTH
// 2908.         - AXI_AUXM_ADDR_WIDTH
// 2918.         - AXI_AUXM_AWUSER_WIDTH
// 2928.         - AXI_AUXM_WUSER_WIDTH
// 2938.         - AXI_AUXM_BUSER_WIDTH
// 2948.         - AXI_AUXM_ARUSER_WIDTH
// 2958.         - AXI_AUXM_RUSER_WIDTH
// 2968.         - AXI_AUXM_ID_WIDTH
// 2978.         - AXI_AUXM_EXMON_WIDTH
// 2988.         - AXI_AUXM_WDEPTH
// 2998.         - AXI_AUXM_MAXRBURSTS
// 3008.         - AXI_AUXM_MAXWBURSTS
// 3018.         - AXI_AUXM_RCAM_OVERFLOW
// 3029.         - AXI_AUXM_RCAM_UNDERFLOW
// 3040.         - AXI_AUXM_WCAM_OVERFLOW
// 3051.         - AXI_AUXM_WCAM_UNDERFLOW
// 3062.         - AXI_AUXM_EXCL_OVERFLOW
// 3074.    2) Combinatorial Logic
// 3079.       a) Masks
// 3083.            - AlignMaskR
// 3105.            - AlignMaskW
// 3127.            - ExclMask
// 3135.            - WdataMask
// 3148.            - RdataMask
// 3154.       b) Increments
// 3158.            - ArAddrIncr
// 3166.            - AwAddrIncr
// 3175.       c) Conversions
// 3179.            - ArLenInBytes
// 3187.            - ArSizeInBits
// 3195.            - AwSizeInBits
// 3204.       d) Other
// 3208.            - ArExclPending
// 3214.            - ArLenPending
// 3219.            - ArCountPending
// 3226.    3) EXCL & LOCK Accesses
// 3230.         - Exclusive Access ID Lookup
// 3356.         - Exclusive Access Storage
// 3411.         - Lock State Machine
// 3452.         - Lock State Register
// 3475.         - Lock Property Logic
// 3585.    4) Content addressable memories (CAMs)
// 3589.         - Read CAMSs (CAM+Shift)
// 3729.         - Write CAMs (CAM+Shift)
// 4113.         - Write Depth array
// 4207.    5) Verilog Functions
// 4211.         - CheckBurst
// 4310.         - CheckStrb
// 4348.         - ReadDataMask
// 4368.         - ByteShift
// 4463.         - ByteCount
// 4510. 
// 4511.  End of File
// 4516.    1) Clear Verilog Defines
// 4538.    2) End of module
//----------------------------------------------------------------------------

`timescale 1ns/1ns

//------------------------------------------------------------------------------
// AXI Standard Defines
//------------------------------------------------------------------------------
`include "Axi.v"


//------------------------------------------------------------------------------
// INDEX: Module: AxiPC
//------------------------------------------------------------------------------
module AxiPC
  (
   // Global Signals
   ACLK,
   ARESETn,

   // Write Address Channel
   AWID,
   AWADDR,
   AWLEN,
   AWSIZE,
   AWBURST,
   AWLOCK,
   AWCACHE,
   AWPROT,
   AWUSER,
   AWVALID,
   AWREADY,

   // Write Channel
   WID,
   WLAST,
   WDATA,
   WSTRB,
   WUSER,
   WVALID,
   WREADY,

   // Write Response Channel
   BID,
   BRESP,
   BUSER,
   BVALID,
   BREADY,

   // Read Address Channel
   ARID,
   ARADDR,
   ARLEN,
   ARSIZE,
   ARBURST,
   ARLOCK,
   ARCACHE,
   ARPROT,
   ARUSER,
   ARVALID,
   ARREADY,

   // Read Channel
   RID,
   RLAST,
   RDATA,
   RRESP,
   RUSER,
   RVALID,
   RREADY,

   // Low power interface
   CACTIVE,
   CSYSREQ,
   CSYSACK
   );


//------------------------------------------------------------------------------
// INDEX:   1) Parameters
//------------------------------------------------------------------------------


  // INDEX:        - Configurable (user can set)
  // =====
  // Parameters below can be set by the user.

  // Set DATA_WIDTH to the data-bus width required
  parameter DATA_WIDTH = 64;         // data bus width, default = 64-bit

  // Select the number of channel ID bits required
  parameter ID_WIDTH = 4;          // (A|W|R|B)ID width

  // Select the size of the USER buses, default = 32-bit
  parameter AWUSER_WIDTH = 32; // width of the user AW sideband field
  parameter WUSER_WIDTH  = 32; // width of the user W  sideband field
  parameter BUSER_WIDTH  = 32; // width of the user B  sideband field
  parameter ARUSER_WIDTH = 32; // width of the user AR sideband field
  parameter RUSER_WIDTH  = 32; // width of the user R  sideband field

  // Write-interleave Depth of monitored slave interface
  parameter WDEPTH = 1;

  // Size of CAMs for storing outstanding read bursts, this should match or
  // exceed the number of outstanding read addresses accepted into the slave
  // interface
  parameter MAXRBURSTS = 16;

  // Size of CAMs for storing outstanding write bursts, this should match or
  // exceed the number of outstanding write bursts into the slave  interface
  parameter MAXWBURSTS = 16;

  // Maximum number of cycles between VALID -> READY high before a warning is
  // generated
  parameter MAXWAITS = 16;

  // OVL instances property_type parameter (0=assert, 1=assume, 2=ignore)
  parameter AXI_ERRM_PropertyType = 0; // default: assert Master is AXI compliant
  parameter AXI_RECM_PropertyType = 0; // default: assert Master is AXI compliant
  parameter AXI_AUXM_PropertyType = 0; // default: assert Master auxiliary logic checks
  //
  parameter AXI_ERRS_PropertyType = 0; // default: assert Slave is AXI compliant
  parameter AXI_RECS_PropertyType = 0; // default: assert Slave is AXI compliant
  parameter AXI_AUXS_PropertyType = 0; // default: assert Slave auxiliary logic checks
  //
  parameter AXI_ERRL_PropertyType = 0; // default: assert LP Int is AXI compliant

  // Recommended Rules Enable
  parameter RecommendOn   = 1'b1;   // enable/disable reporting of all  AXI_REC*_* rules
  parameter RecMaxWaitOn  = 1'b1;   // enable/disable reporting of just AXI_REC*_MAX_WAIT rules

  // Set ADDR_WIDTH to the address-bus width required
  parameter ADDR_WIDTH = 32;         // address bus width, default = 32-bit

  // Set EXMON_WIDTH to the exclusive access monitor width required
  parameter EXMON_WIDTH = 4;         // exclusive access width, default = 4-bit

  // INDEX:        - Calculated (user should not override)
  // =====
  // Do not override the following parameters: they must be calculated exactly
  // as shown below
  parameter DATA_MAX   = DATA_WIDTH-1; // data max index
  parameter ADDR_MAX   = ADDR_WIDTH-1; // address max index
  parameter STRB_WIDTH = DATA_WIDTH/8; // WSTRB width
  parameter STRB_MAX   = STRB_WIDTH-1; // WSTRB max index
  parameter STRB_1     = {{STRB_MAX{1'b0}}, 1'b1};  // value 1 in strobe width
  parameter ID_MAX     = ID_WIDTH-1;   // ID max index
  parameter EXMON_MAX  = EXMON_WIDTH-1;       // EXMON max index
  parameter EXMON_HI   = {EXMON_WIDTH{1'b1}}; // EXMON max value

  parameter AWUSER_MAX = AWUSER_WIDTH-1; // AWUSER max index
  parameter  WUSER_MAX =  WUSER_WIDTH-1; // WUSER  max index
  parameter  BUSER_MAX =  BUSER_WIDTH-1; // BUSER  max index
  parameter ARUSER_MAX = ARUSER_WIDTH-1; // ARUSER max index
  parameter  RUSER_MAX =  RUSER_WIDTH-1; // RUSER  max index

  // FLAGLL/LO/UN WSTRB16...WSTRB1 ID BURST ASIZE ALEN LOCKED EXCL LAST ADDR[6:0]
  parameter ADDRLO   = 0;                 // ADDRLO   =   0
  parameter ADDRHI   = 6;                 // ADDRHI   =   6
  parameter EXCL     = ADDRHI + 1;        // Transaction is exclusive
  parameter LOCKED   = EXCL + 1;          // Transaction is locked
  parameter ALENLO   = LOCKED + 1;        // ALENLO   =   9
  parameter ALENHI   = ALENLO + 3;        // ALENHI   =  12
  parameter ASIZELO  = ALENHI + 1;        // ASIZELO  =  13
  parameter ASIZEHI  = ASIZELO + 2;       // ASIZEHI  =  15
  parameter BURSTLO  = ASIZEHI + 1;       // BURSTLO  =  16
  parameter BURSTHI  = BURSTLO + 1;       // BURSTHI  =  17
  parameter IDLO     = BURSTHI + 1;       // IDLO     =  18
  parameter IDHI     = IDLO+ID_MAX;       // IDHI     =  21 if ID_WIDTH=4
  parameter STRB1LO  = IDHI+1;            // STRB1LO  =  22 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB1HI  = STRB1LO+STRB_MAX;  // STRB1HI  =  29 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB2LO  = STRB1HI+1;         // STRB2LO  =  30 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB2HI  = STRB2LO+STRB_MAX;  // STRB2HI  =  37 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB3LO  = STRB2HI+1;         // STRB3LO  =  38 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB3HI  = STRB3LO+STRB_MAX;  // STRB3HI  =  45 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB4LO  = STRB3HI+1;         // STRB4LO  =  46 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB4HI  = STRB4LO+STRB_MAX;  // STRB4HI  =  53 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB5LO  = STRB4HI+1;         // STRB5LO  =  54 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB5HI  = STRB5LO+STRB_MAX;  // STRB5HI  =  61 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB6LO  = STRB5HI+1;         // STRB6LO  =  62 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB6HI  = STRB6LO+STRB_MAX;  // STRB6HI  =  69 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB7LO  = STRB6HI+1;         // STRB7LO  =  70 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB7HI  = STRB7LO+STRB_MAX;  // STRB7HI  =  77 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB8LO  = STRB7HI+1;         // STRB8LO  =  78 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB8HI  = STRB8LO+STRB_MAX;  // STRB8HI  =  85 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB9LO  = STRB8HI+1;         // STRB9LO  =  86 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB9HI  = STRB9LO+STRB_MAX;  // STRB9HI  =  93 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB10LO = STRB9HI+1;         // STRB10LO =  94 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB10HI = STRB10LO+STRB_MAX; // STRB10HI = 101 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB11LO = STRB10HI+1;        // STRB11LO = 102 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB11HI = STRB11LO+STRB_MAX; // STRB11HI = 109 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB12LO = STRB11HI+1;        // STRB12LO = 110 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB12HI = STRB12LO+STRB_MAX; // STRB12HI = 117 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB13LO = STRB12HI+1;        // STRB13LO = 118 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB13HI = STRB13LO+STRB_MAX; // STRB13HI = 125 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB14LO = STRB13HI+1;        // STRB14LO = 126 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB14HI = STRB14LO+STRB_MAX; // STRB14HI = 133 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB15LO = STRB14HI+1;        // STRB15LO = 134 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB15HI = STRB15LO+STRB_MAX; // STRB15HI = 141 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB16LO = STRB15HI+1;        // STRB16LO = 142 if ID_WIDTH=4 & STRB_MAX=7
  parameter STRB16HI = STRB16LO+STRB_MAX; // STRB16HI = 149 if ID_WIDTH=4 & STRB_MAX=7
  parameter FLAGUN   = STRB16HI+1;        // Seen coincident with unlocked transactions
  parameter FLAGLO   = FLAGUN+1;          // Seen coincident with locked transactions
  parameter FLAGLL   = FLAGLO+1;          // Seen coincident with lock last transaction

  parameter WBURSTMAX = FLAGLL; // Write burst register array maximum
  parameter RBURSTMAX = IDHI;   // Read burst register array maximum


//------------------------------------------------------------------------------
// INDEX:   2) Inputs (no outputs)
//------------------------------------------------------------------------------


  // INDEX:        - Global Signals
  // =====
  input                ACLK;        // AXI Clock
  input                ARESETn;     // AXI Reset


  // INDEX:        - Write Address Channel
  // =====
  input     [ID_MAX:0] AWID;
  input   [ADDR_MAX:0] AWADDR;
  input          [3:0] AWLEN;
  input          [2:0] AWSIZE;
  input          [1:0] AWBURST;
  input          [3:0] AWCACHE;
  input          [2:0] AWPROT;
  input          [1:0] AWLOCK;
  input [AWUSER_MAX:0] AWUSER;
  input                AWVALID;
  input                AWREADY;


  // INDEX:        - Write Data Channel
  // =====
  input     [ID_MAX:0] WID;
  input   [DATA_MAX:0] WDATA;
  input   [STRB_MAX:0] WSTRB;
  input  [WUSER_MAX:0] WUSER;
  input                WLAST;
  input                WVALID;
  input                WREADY;


  // INDEX:        - Write Response Channel
  // =====
  input     [ID_MAX:0] BID;
  input          [1:0] BRESP;
  input  [BUSER_MAX:0] BUSER;
  input                BVALID;
  input                BREADY;


  // INDEX:        - Read Address Channel
  // =====
  input     [ID_MAX:0] ARID;
  input   [ADDR_MAX:0] ARADDR;
  input          [3:0] ARLEN;
  input          [2:0] ARSIZE;
  input          [1:0] ARBURST;
  input          [3:0] ARCACHE;
  input          [2:0] ARPROT;
  input          [1:0] ARLOCK;
  input [ARUSER_MAX:0] ARUSER;
  input                ARVALID;
  input                ARREADY;


  // INDEX:        - Read Data Channel
  // =====
  input     [ID_MAX:0] RID;
  input   [DATA_MAX:0] RDATA;
  input          [1:0] RRESP;
  input  [RUSER_MAX:0] RUSER;
  input                RLAST;
  input                RVALID;
  input                RREADY;

  // INDEX:        - Low Power Interface
  // =====
  input                CACTIVE;
  input                CSYSREQ;
  input                CSYSACK;


//------------------------------------------------------------------------------
// INDEX:   3) Wire and Reg Declarations
//------------------------------------------------------------------------------

  // User signal definitions are defined as weak pull-down in the case
  // that they are unconnected.
  tri0 [AWUSER_MAX:0] AWUSER;
  tri0  [WUSER_MAX:0] WUSER;
  tri0  [BUSER_MAX:0] BUSER;
  tri0 [ARUSER_MAX:0] ARUSER;
  tri0  [RUSER_MAX:0] RUSER;

  // Low power interface signals are defined as weak pull-up in the case
  // that they are unconnected.
  tri1                CACTIVE;
  tri1                CSYSREQ;
  tri1                CSYSACK;

  // Write CAMs
  integer            WIndex;
  reg  [WBURSTMAX:0] WBurstCam[1:MAXWBURSTS]; // store outstanding write bursts
  reg          [4:0] WCountCam[1:MAXWBURSTS]; // number of write data stored
  reg                WLastCam[1:MAXWBURSTS];  // WLAST for outstanding writes
  reg                WAddrCam[1:MAXWBURSTS];  // flag for valid write addr
  reg                BRespCam[1:MAXWBURSTS];  // flag for valid write resp
  reg                nWAddrTrans;    // flag for an empty WAddrCam
  reg                UnlockedInWCam; // At least one unlocked read in WBurstCam
  reg                LockedInWCam;   // At least one locked read in WBurstCam
  reg                FlagUNInWCam;   // At least one write transaction has FLAGUN set
  reg                FlagLOInWCam;   // At least one write transaction has FLAGLO set
  reg                FlagLLInWCam;   // At least one write transaction has FLAGLL set

  // WDepth array
  reg     [ID_MAX:0] WdepthId[WDEPTH:0]; // Write ID lookup table
  reg     [WDEPTH:0] WdepthIdValid;      // Write ID lookup table entry valid
  reg                WdepthIdDelta;      // Write ID lookup table has changed
  wire               WdepthIdFull;       // Write ID lookup table is full
  reg         [15:0] WdepthIdFreePtr;    // Write ID lookup table next free entry
  wire        [15:0] WdepthIdWrPtr;      // Write ID lookup table write pointer
  reg                WdepthWMatch;       // Write ID lookup table WID match found
  reg         [15:0] WdepthWId;          // Write ID lookup table matching WID reference
  integer            WidDepth;           // Number of write data IDs currently in use

  // Read CAMs
  reg  [RBURSTMAX:0] RBurstCam[1:MAXRBURSTS];
  reg          [4:0] RCountCam[1:MAXRBURSTS];
  integer            RIndex;
  integer            RIndexNext;
  wire               RPop;
  wire               RPush;
  wire               nROutstanding;  // flag for an empty RBurstCam
  reg                RIdCamDelta;    // flag indicates that RidCam has changed
  reg                UnlockedInRCam; // flag for unlocked reads in RBurstCam
  reg                LockedInRCam;   // flag for locked reads in RBurstCam

  // Protocol error flags
  wire               WriteDataNumError; // flag for AXI_ERRM_WDATA_NUM rule
  reg                AWDataNumError;  // flag to derive WriteDataNumError
  reg                WDataNumError;   // flag to derive WriteDataNumError
  reg                WDataOrderError; // flag for AXI_ERRM_WDATA_ORDER rule
  reg                BrespError;      // flag for AXI_ERRS_BRESP rule
  reg                BrespExokError;  // flag for AXI_ERRS_BRESP_EXOKAY rule
  wire               StrbError;       // flag for AXI_ERRM_WSTRB rule
  reg                AWStrbError;     // flag to derive StrbError
  reg                BStrbError;      // flag to derive StrbError

  // Protocol recommendation flags
  reg                BrespLeadingRec; // flag for AXI_RECS_BRESP rule

  // signals for checking for match in ID CAMs
  integer            AidMatch;
  integer            WidMatch;
  integer            RidMatch;
  integer            BidMatch;

  reg          [6:0] AlignMaskR; // mask for checking read address alignment
  reg          [6:0] AlignMaskW; // mask for checking write address alignment

  // signals for Address Checking
  reg   [ADDR_MAX:0] ArAddrIncr;
  reg   [ADDR_MAX:0] AwAddrIncr;

  // signals for Data Checking
  wire  [DATA_MAX:0] RdataMask;
  reg   [DATA_MAX:0] WdataMask;
  reg         [10:0] ArSizeInBits;
  reg         [10:0] AwSizeInBits;
  reg         [11:0] ArLenInBytes;
  wire         [4:0] ArLenPending;
  wire         [4:0] ArCountPending;
  wire               ArExclPending;

  // Lock signals
  wire               AWLockNew;     // Initial locking write address valid for a locked sequence
  wire               ARLockNew;     // Initial locking read address valid for a locked sequence
  wire               AWLockLastNew; // Unlocking write address valid for a locked sequence
  wire               ARLockLastNew; // Unlocking read address valid for a locked sequence
  wire               LockedRead;    // At least one locked read on the bus
  wire               UnlockedRead;  // At least one unlocked read on the bus
  wire               LockedWrite;   // At least one locked write on the bus
  wire               UnlockedWrite; // At least one unlocked write on the bus
  reg                PrevAWVALID;   // Prev cycle had AWVALID=1
  reg                PrevAWREADY;   // Prev cycle had AWREADY=1
  reg                PrevARVALID;   // Prev cycle had ARVALID=1
  reg                PrevARREADY;   // Prev cycle had ARREADY=1
  wire               AWNew;         // New valid write address in current cycle
  wire               ARNew;         // New valid read address in current cycle
  reg          [1:0] LockState;
  reg          [1:0] LockStateNext;
  reg     [ID_MAX:0] LockIdNext;
  reg     [ID_MAX:0] LockId;
  reg          [3:0] LockCacheNext;
  reg          [3:0] LockCache;
  reg          [2:0] LockProtNext;
  reg          [2:0] LockProt;
  reg   [ADDR_MAX:0] LockAddrNext;
  reg   [ADDR_MAX:0] LockAddr;

  // arrays to store exclusive access control info
  reg     [ID_MAX:0] ExclId[EXMON_HI:0];
  reg                ExclIdDelta;
  reg   [EXMON_HI:0] ExclIdValid;
  wire               ExclIdFull;
  wire               ExclIdOverflow;
  reg  [EXMON_MAX:0] ExclIdFreePtr;
  wire [EXMON_MAX:0] ExclIdWrPtr;
  reg  [EXMON_MAX:0] ExclAwId;
  reg                ExclAwMatch;
  reg  [EXMON_MAX:0] ExclArId;
  reg                ExclArMatch;
  reg  [EXMON_MAX:0] ExclRId;
  reg                ExclRMatch;
  reg                ExclReadAddr[EXMON_HI:0]; // tracks excl read addr
  reg                ExclReadData[EXMON_HI:0]; // tracks excl read data
  reg   [ADDR_MAX:0] ExclAddr[EXMON_HI:0];
  reg          [2:0] ExclSize[EXMON_HI:0];
  reg          [3:0] ExclLen[EXMON_HI:0];
  reg          [1:0] ExclBurst[EXMON_HI:0];
  reg          [3:0] ExclCache[EXMON_HI:0];
  reg          [2:0] ExclProt[EXMON_HI:0];
  reg [AWUSER_MAX:0] ExclUser[EXMON_HI:0];
  reg         [10:0] ExclMask; // mask to check alignment of exclusive address

  // Signals to avoid feeding parameters directly into assertions as this can
  // stop assertions triggering in some cases
  reg                i_RecommendOn;
  reg                i_RecMaxWaitOn;


//------------------------------------------------------------------------------
// INDEX:   4) Verilog Defines
//------------------------------------------------------------------------------


  // INDEX:        - Lock FSM States
  // =====
  // Lock FSM States (3-state FSM, so one state encoding is not used)
  `define AXI_AUX_ST_UNLOCKED  2'b00
  `define AXI_AUX_ST_LOCKED    2'b01
  `define AXI_AUX_ST_LOCK_LAST 2'b10
  `define AXI_AUX_ST_NOT_USED  2'b11


  // INDEX:        - Clock and Reset
  // =====
  // Can be overridden by user for a clock enable.
  //
  // Can also be used to clock SVA on negedge (to avoid race hazards with
  // auxiliary logic) by compiling with the override:
  //
  //   +define+AXI_SVA_CLK=~ACLK
  // 
  // SVA: Assertions
  `ifdef AXI_SVA_CLK
  `else
     `define AXI_SVA_CLK ACLK
  `endif
  //
  `ifdef AXI_SVA_RSTn
  `else
     `define AXI_SVA_RSTn ARESETn
  `endif
  // 
  // AUX: Auxiliary Logic
  `ifdef AXI_AUX_CLK
  `else
     `define AXI_AUX_CLK ACLK
  `endif
  //
  `ifdef AXI_AUX_RSTn
  `else
     `define AXI_AUX_RSTn ARESETn
  `endif


//------------------------------------------------------------------------------
// INDEX:   5) Initialize simulation
//------------------------------------------------------------------------------
  initial
    begin

       // INDEX:        - Format for time reporting
       // =====
       // Format for time reporting
       $timeformat(-9, 0, " ns", 0);


       // INDEX:        - Indicate version and release state of AxiPC
       // =====
       $display("AXI_INFO: Running AxiPC version BP062-BU-01000-r0p1-00rel0");


       // INDEX:        - Warn if any/some recommended rules are disabled
       // =====
       if (~RecommendOn)
         // All AXI_REC*_* rules disabled
         $display("AXI_WARN: All recommended AXI rules have been disabled by the RecommendOn parameter");
       else if (~RecMaxWaitOn)
         // Just AXI_REC*_MAX_WAIT rules disabled
         $display("AXI_WARN: Five recommended MAX_WAIT rules have been disabled by the RecMaxWaitOn parameter");

       if (RecommendOn)
         i_RecommendOn = 1'b1;
       else
         i_RecommendOn = 1'b0;

       if (RecMaxWaitOn)
         i_RecMaxWaitOn = 1'b1;
       else
         i_RecMaxWaitOn = 1'b0;


       // INDEX:        - Warn if any/some channel rules are ignored
       // =====
       if (AXI_ERRM_PropertyType > 0) $display("AXI_WARN: The AXI_ERRM_PropertyType parameter is currently not used by the SVA version");
       if (AXI_RECM_PropertyType > 0) $display("AXI_WARN: The AXI_RECM_PropertyType parameter is currently not used by the SVA version");
       if (AXI_AUXM_PropertyType > 0) $display("AXI_WARN: The AXI_AUXM_PropertyType parameter is currently not used by the SVA version");
       //
       if (AXI_ERRS_PropertyType > 0) $display("AXI_WARN: The AXI_ERRS_PropertyType parameter is currently not used by the SVA version");
       if (AXI_RECS_PropertyType > 0) $display("AXI_WARN: The AXI_RECS_PropertyType parameter is currently not used by the SVA version");
       if (AXI_AUXS_PropertyType > 0) $display("AXI_WARN: The AXI_AUXS_PropertyType parameter is currently not used by the SVA version");
       //
       if (AXI_ERRL_PropertyType > 0) $display("AXI_WARN: The AXI_ERRL_PropertyType parameter is currently not used by the SVA version");

    end


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Write Address Channel (*_AW*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_AWADDR_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  //
  // Only need to check INCR bursts since:
  //
  //   a) FIXED bursts cannot violate the 4kB boundary by definition
  //
  //   b) WRAP bursts always stay within a <4kB region because of the wrap
  //      address boundary.  The biggest WRAP burst possible has length 16,
  //      size 128 bytes (1024 bits), so it can transfer 2048 bytes. The
  //      individual transfer addresses wrap at a 2048 byte address boundary,
  //      and the max data transferred in also 2048 bytes, so a 4kB boundary
  //      can never be broken.
  property AXI_ERRM_AWADDR_BOUNDARY;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWBURST,AWADDR})) &
          AWVALID & (AWBURST == `AXI_ABURST_INCR)
      |-> (AwAddrIncr[ADDR_MAX:12] == AWADDR[ADDR_MAX:12]);
  endproperty
  axi_errm_awaddr_boundary: assert property (AXI_ERRM_AWADDR_BOUNDARY) else
   $error("AXI_ERRM_AWADDR_BOUNDARY. A write burst cannot cross a 4kbyte boundary. Spec: section 4.1 on page 4-2.");


  // INDEX:        - AXI_ERRM_AWADDR_WRAP_ALIGN
  // =====
  property AXI_ERRM_AWADDR_WRAP_ALIGN;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWBURST,AWADDR})) &
          AWVALID & (AWBURST == `AXI_ABURST_WRAP)
      |-> ((AWADDR[6:0] & AlignMaskW) == AWADDR[6:0]);
  endproperty
  axi_errm_awaddr_wrap_align: assert property (AXI_ERRM_AWADDR_WRAP_ALIGN) else
   $error("AXI_ERRM_AWADDR_WRAP_ALIGN. A write transaction with burst type WRAP must have an aligned address. Spec: section 4.4.3 on page 4-6.");


  // INDEX:        - AXI_ERRM_AWBURST
  // =====
  property AXI_ERRM_AWBURST;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWBURST})) &
          AWVALID
      |-> (AWBURST != 2'b11);
  endproperty
  axi_errm_awburst: assert property (AXI_ERRM_AWBURST) else
   $error("AXI_ERRM_AWBURST. When AWVALID is high, a value of 2'b11 on AWBURST is not permitted. Spec: table 4-3 on page 4-5.");


  // INDEX:        - AXI_ERRM_AWCACHE
  // =====
  property AXI_ERRM_AWCACHE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWCACHE})) &
          AWVALID & ~AWCACHE[1]
      |-> (AWCACHE[3:2] == 2'b00);
  endproperty
  axi_errm_awcache: assert property (AXI_ERRM_AWCACHE) else
   $error("AXI_ERRM_AWCACHE. When AWVALID is high, if AWCACHE[1] is low then AWCACHE[3] and AWCACHE[2] must also be low. Spec: table 5-1 on page 5-3.");


  // INDEX:        - AXI_ERRM_AWLEN_WRAP
  // =====
  property AXI_ERRM_AWLEN_WRAP;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWBURST,AWLEN})) &
          AWVALID & (AWBURST == `AXI_ABURST_WRAP)
      |-> (AWLEN == `AXI_ALEN_2 ||
           AWLEN == `AXI_ALEN_4 ||
           AWLEN == `AXI_ALEN_8 ||
           AWLEN == `AXI_ALEN_16);
  endproperty
  axi_errm_awlen_wrap: assert property (AXI_ERRM_AWLEN_WRAP) else
   $error("AXI_ERRM_AWLEN_WRAP. A write transaction with burst type WRAP must have length 2, 4, 8 or 16. Spec: section 4.4.3 on page 4-6.");


  // INDEX:        - AXI_ERRM_AWLOCK
  // =====
  property AXI_ERRM_AWLOCK;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWLOCK})) &
          AWVALID
      |-> (AWLOCK != 2'b11);
  endproperty
  axi_errm_awlock: assert property (AXI_ERRM_AWLOCK) else
   $error("AXI_ERRM_AWLOCK. When AWVALID is high, a value of 2'b11 on AWLOCK is not permitted. Spec: table 6-1 on page 6-2.");


  // INDEX:        - AXI_ERRM_AWLOCK_END
  // =====
  property AXI_ERRM_AWLOCK_END;
    @(posedge `AXI_SVA_CLK)
          (LockState == `AXI_AUX_ST_LOCK_LAST) & // the unlocking transfer has begun and should have completed
          AWNew                                  // new valid write address
      |-> nROutstanding &                        // no outstanding reads
          nWAddrTrans &                          // no writes other than leading write data (checked separately)
          !FlagLLInWCam;                         // no leading write transactions from previous lock last period
  endproperty
  axi_errm_awlock_end: assert property (AXI_ERRM_AWLOCK_END) else
   $error("AXI_ERRM_AWLOCK_END. A master must wait for an unlocked transaction at the end of a locked sequence to complete before issuing another write transaction. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_AWLOCK_ID
  // =====
  property AXI_ERRM_AWLOCK_ID;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWID,AWLOCK,
                        ARID,ARLOCK}))
      |->
          // case for in lock or going into lock last
          !(AWNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid write address in a locked sequence
           (AWID != LockId)                               // id value does not match current lock id
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&      // in unlocked or lock last state
           (AWID != ARID)                                 // lock id values do not agree
          );
  endproperty
  axi_errm_awlock_id: assert property (AXI_ERRM_AWLOCK_ID) else
   $error("AXI_ERRM_AWLOCK_ID. A sequence of locked transactions must use a single ID. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_AWLOCK_LAST
  // =====
  property AXI_ERRM_AWLOCK_LAST;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID})) &
          AWLockLastNew   // going into lock last with a locked write
      |-> nROutstanding & // no outstanding reads
          nWAddrTrans &   // no writes other than leading write data (checked separately)
          (WIndex <= 2) & // at most there can only be one leading write transaction
          ~ARVALID &      // no read activity
          !FlagLOInWCam;  // no leading write transactions from previous locked period
  endproperty
  axi_errm_awlock_last: assert property (AXI_ERRM_AWLOCK_LAST) else
   $error("AXI_ERRM_AWLOCK_LAST. A master must wait for all locked transactions to complete before issuing an unlocking write transaction. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_AWLOCK_START
  // =====
  property AXI_ERRM_AWLOCK_START;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARLOCK})) &
          AWLockNew                                    // going into locked with a locked write
      |-> nROutstanding &                              // no outstanding reads
          nWAddrTrans &                                // no writes other than leading write data (checked separately)
          !(ARVALID & (ARLOCK != `AXI_ALOCK_LOCKED)) & // allow a new read but only if it is locked
          !FlagUNInWCam &                              // no leading write transactions from previous unlocked period
          !FlagLLInWCam;                               // no leading write transactions from previous lock last period
  endproperty
  axi_errm_awlock_start: assert property (AXI_ERRM_AWLOCK_START) else
   $error("AXI_ERRM_AWLOCK_START. A master must wait for all outstanding transactions to complete before issuing a write transaction which is the first in a locked sequence. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_AWSIZE
  // =====
  // Deliberately keeping AwSizeInBits logic outside of assertion, to
  // simplify formal-proofs flow.
  property AXI_ERRM_AWSIZE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWSIZE})) &
          AWVALID
      |-> (AwSizeInBits <= DATA_WIDTH);
  endproperty
  axi_errm_awsize: assert property (AXI_ERRM_AWSIZE) else
   $error("AXI_ERRM_AWSIZE. The size of a write transfer must not exceed the width of the data port. Spec: section 4.3 on page 4-4.");


  // INDEX:        - AXI_ERRM_AWVALID_RESET
  // =====
  property AXI_ERRM_AWVALID_RESET;
    @(posedge `AXI_SVA_CLK)
          !(`AXI_SVA_RSTn) & !($isunknown(`AXI_SVA_RSTn))
      ##1   `AXI_SVA_RSTn
      |-> !AWVALID;
  endproperty
  axi_errm_awvalid_reset: assert property (AXI_ERRM_AWVALID_RESET) else
   $error("AXI_ERRM_AWVALID_RESET. AWVALID must be low in the cycle when ARESETn first goes high. Spec: section 11.1.2 on page 11-2.");


  // INDEX:        - AXI_RECM_AWLOCK_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  property AXI_RECM_AWLOCK_BOUNDARY;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWADDR,AWLOCK,
                        ARADDR,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(AWNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid write address in a locked sequence
           (AWADDR[ADDR_MAX:12] != LockAddr[ADDR_MAX:12]) // address does not match current lock region
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&      // in unlocked or lock last state
           (AWADDR[ADDR_MAX:12] != ARADDR[ADDR_MAX:12])   // lock address region values do not agree
          );
  endproperty
  axi_recm_awlock_boundary: assert property (AXI_RECM_AWLOCK_BOUNDARY) else
   $warning("AXI_RECM_AWLOCK_BOUNDARY. It is recommended that all locked transaction sequences are kept within the same 4KB address region. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_RECM_AWLOCK_CTRL 
  // =====
  property AXI_RECM_AWLOCK_CTRL;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWPROT,AWCACHE,AWLOCK,
                        ARPROT,ARCACHE,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(AWNew && (LockState == `AXI_AUX_ST_LOCKED) &&   // new valid write address in a locked sequence
           ((AWPROT != LockProt) || (AWCACHE != LockCache)) // PROT or CACHE values do not match current lock
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&       // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&        // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&        // in unlocked or lock last state
           ((AWPROT != ARPROT) || (AWCACHE != ARCACHE))     // lock PROT or CACHE values do not agree
          );
  endproperty
  axi_recm_awlock_ctrl: assert property (AXI_RECM_AWLOCK_CTRL) else
   $warning("AXI_RECM_AWLOCK_CTRL. It is recommended that a master should not change AxPROT or AxCACHE during a sequence of locked accesses. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_RECM_AWLOCK_NUM
  // =====
  property AXI_RECM_AWLOCK_NUM;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWLOCK,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(AWNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid write address in a locked sequence
           (AWLOCK == `AXI_ALOCK_LOCKED)                  // write is locked
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST))         // in unlocked or lock last state
          );
  endproperty
  axi_recm_awlock_num: assert property (AXI_RECM_AWLOCK_NUM) else
   $warning("AXI_RECM_AWLOCK_NUM. It is recommended that locked transaction sequences are limited to two transactions. Spec: section 6.3 on page 6-7.");


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_AWADDR_STABLE
  // =====
  property AXI_ERRM_AWADDR_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWADDR})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWADDR);
  endproperty
  axi_errm_awaddr_stable: assert property (AXI_ERRM_AWADDR_STABLE) else
   $error("AXI_ERRM_AWADDR_STABLE. AWADDR must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWBURST_STABLE
  // =====
  property AXI_ERRM_AWBURST_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWBURST})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWBURST);
  endproperty
  axi_errm_awburst_stable: assert property (AXI_ERRM_AWBURST_STABLE) else
   $error("AXI_ERRM_AWBURST_STABLE. AWBURST must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWCACHE_STABLE
  // =====
  property AXI_ERRM_AWCACHE_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWCACHE})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWCACHE);
  endproperty
  axi_errm_awcache_stable: assert property (AXI_ERRM_AWCACHE_STABLE) else
   $error("AXI_ERRM_AWCACHE_STABLE. AWCACHE must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWID_STABLE
  // =====
  property AXI_ERRM_AWID_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWID})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWID);
  endproperty
  axi_errm_awid_stable: assert property (AXI_ERRM_AWID_STABLE) else
   $error("AXI_ERRM_AWID_STABLE. AWID must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWLEN_STABLE
  // =====
  property AXI_ERRM_AWLEN_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWLEN})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWLEN);
  endproperty
  axi_errm_awlen_stable: assert property (AXI_ERRM_AWLEN_STABLE) else
   $error("AXI_ERRM_AWLEN_STABLE. AWLEN must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWLOCK_STABLE
  // =====
  property AXI_ERRM_AWLOCK_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWLOCK})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWLOCK);
  endproperty
  axi_errm_awlock_stable: assert property (AXI_ERRM_AWLOCK_STABLE) else
   $error("AXI_ERRM_AWLOCK_STABLE. AWLOCK must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWPROT_STABLE
  // =====
  property AXI_ERRM_AWPROT_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWPROT})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWPROT);
  endproperty
  axi_errm_awprot_stable: assert property (AXI_ERRM_AWPROT_STABLE) else
   $error("AXI_ERRM_AWPROT_STABLE. AWPROT must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWSIZE_STABLE
  // =====
  property AXI_ERRM_AWSIZE_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWSIZE})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWSIZE);
  endproperty
  axi_errm_awsize_stable: assert property (AXI_ERRM_AWSIZE_STABLE) else
   $error("AXI_ERRM_AWSIZE_STABLE. AWSIZE must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_AWVALID_STABLE
  // =====
  property AXI_ERRM_AWVALID_STABLE;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & AWVALID & !AWREADY & !($isunknown({AWVALID,AWREADY}))
      ##1 `AXI_SVA_RSTn
      |-> AWVALID;
  endproperty
  axi_errm_awvalid_stable: assert property (AXI_ERRM_AWVALID_STABLE) else
   $error("AXI_ERRM_AWVALID_STABLE. Once AWVALID is asserted, it must remain asserted until AWREADY is high. Spec: section 3.1.1 on page 3-2.");


  // INDEX:        - AXI_RECS_AWREADY_MAX_WAIT
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI_RECS_AWREADY_MAX_WAIT;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown({AWVALID,AWREADY})) &
      i_RecommendOn                            & // Parameter that can disable all AXI_REC*_* rules
      i_RecMaxWaitOn                           & // Parameter that can disable just AXI_REC*_MAX_WAIT rules
                         ( AWVALID & !AWREADY) 
      |-> ##[1:MAXWAITS] (!AWVALID |  AWREADY);  // READY=1 within MAXWAITS cycles (or VALID=0)
  endproperty
  axi_recs_awready_max_wait: assert property (AXI_RECS_AWREADY_MAX_WAIT) else
   $warning("AXI_RECS_AWREADY_MAX_WAIT. AWREADY should be asserted within MAXWAITS cycles of AWVALID being asserted.");  


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRM_AWADDR_X
  // =====
  property AXI_ERRM_AWADDR_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWADDR);
  endproperty
  axi_errm_awaddr_x: assert property (AXI_ERRM_AWADDR_X) else
   $error("AXI_ERRM_AWADDR_X. When AWVALID is high, a value of X on AWADDR is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWBURST_X
  // =====
  property AXI_ERRM_AWBURST_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWBURST);
  endproperty
  axi_errm_awburst_x: assert property (AXI_ERRM_AWBURST_X) else
   $error("AXI_ERRM_AWBURST_X. When AWVALID is high, a value of X on AWBURST is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWCACHE_X
  // =====
  property AXI_ERRM_AWCACHE_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWCACHE);
  endproperty
  axi_errm_awcache_x: assert property (AXI_ERRM_AWCACHE_X) else
   $error("AXI_ERRM_AWCACHE_X. When AWVALID is high, a value of X on AWCACHE is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWID_X
  // =====
  property AXI_ERRM_AWID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWID);
  endproperty
  axi_errm_awid_x: assert property (AXI_ERRM_AWID_X) else
   $error("AXI_ERRM_AWID_X. When AWVALID is high, a value of X on AWID is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWLEN_X
  // =====
  property AXI_ERRM_AWLEN_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWLEN);
  endproperty
  axi_errm_awlen_x: assert property (AXI_ERRM_AWLEN_X) else
   $error("AXI_ERRM_AWLEN_X. When AWVALID is high, a value of X on AWLEN is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWLOCK_X
  // =====
  property AXI_ERRM_AWLOCK_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWLOCK);
  endproperty
  axi_errm_awlock_x: assert property (AXI_ERRM_AWLOCK_X) else
   $error("AXI_ERRM_AWLOCK_X. When AWVALID is high, a value of X on AWLOCK is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWPROT_X
  // =====
  property AXI_ERRM_AWPROT_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWPROT);
  endproperty
  axi_errm_awprot_x: assert property (AXI_ERRM_AWPROT_X) else
   $error("AXI_ERRM_AWPROT_X. When AWVALID is high, a value of X on AWPROT is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWSIZE_X
  // =====
  property AXI_ERRM_AWSIZE_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWSIZE);
  endproperty
  axi_errm_awsize_x: assert property (AXI_ERRM_AWSIZE_X) else
   $error("AXI_ERRM_AWSIZE_X. When AWVALID is high, a value of X on AWSIZE is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_AWVALID_X
  // =====
  property AXI_ERRM_AWVALID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(AWVALID);
  endproperty
  axi_errm_awvalid_x: assert property (AXI_ERRM_AWVALID_X) else
   $error("AXI_ERRM_AWVALID_X. When not in reset, a value of X on AWVALID is not permitted.");


  // INDEX:        - AXI_ERRS_AWREADY_X
  // =====
  property AXI_ERRS_AWREADY_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(AWREADY);
  endproperty
  axi_errs_awready_x: assert property (AXI_ERRS_AWREADY_X) else
   $error("AXI_ERRS_AWREADY_X. When not in reset, a value of X on AWREADY is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Write Data Channel (*_W*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_WDATA_NUM
  // =====
  // This will fire in one of the following situations:
  // 1) Write data arrives and WLAST set and WDATA count is not equal to AWLEN
  // 2) Write data arrives and WLAST not set and WDATA count is equal to AWLEN
  // 3) ADDR arrives, WLAST already received and WDATA count not equal to AWLEN
  property AXI_ERRM_WDATA_NUM;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(WriteDataNumError))
      |-> ~WriteDataNumError;
  endproperty
  axi_errm_wdata_num: assert property (AXI_ERRM_WDATA_NUM) else
   $error("AXI_ERRM_WDATA_NUM. The number of write data items must match AWLEN for the corresponding address. Spec: table 4-1 on page 4-3.");


  // INDEX:        - AXI_ERRM_WDATA_ORDER
  // =====
  property AXI_ERRM_WDATA_ORDER;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(WDataOrderError))
      |-> ~WDataOrderError;
  endproperty
  axi_errm_wdata_order: assert property (AXI_ERRM_WDATA_ORDER) else
   $error("AXI_ERRM_WDATA_ORDER. The order in which addresses and the first write data item are produced must match. Spec: section 8.5 on page 8-6.");


  // INDEX:        - AXI_ERRM_WDEPTH
  // =====
  property AXI_ERRM_WDEPTH;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WidDepth})) &
          WVALID & WREADY
      |-> (WidDepth <= WDEPTH);
  endproperty
  axi_errm_wdepth: assert property (AXI_ERRM_WDEPTH) else
   $error("AXI_ERRM_WDEPTH. A master can interleave a maximum of WDEPTH write data bursts. Spec: section 8.5 on page 8-6.");


  // INDEX:        - AXI_ERRM_WSTRB
  // =====
  property AXI_ERRM_WSTRB;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(StrbError))
      |-> ~StrbError;
  endproperty
  axi_errm_wstrb: assert property (AXI_ERRM_WSTRB) else
   $error("AXI_ERRM_WSTRB. Write strobes must only be asserted for the correct byte lanes as determined from start address, transfer size and beat number. Spec: section 9.2 on page 9-3.");


  // INDEX:        - AXI_ERRM_WVALID_RESET
  // =====
  property AXI_ERRM_WVALID_RESET;
    @(posedge `AXI_SVA_CLK)
          !(`AXI_SVA_RSTn) & !($isunknown(`AXI_SVA_RSTn))
      ##1   `AXI_SVA_RSTn
      |-> !WVALID;
  endproperty
  axi_errm_wvalid_reset: assert property (AXI_ERRM_WVALID_RESET) else
   $error("AXI_ERRM_WVALID_RESET. WVALID must be low in the cycle when ARESETn first goes high. Spec: section 11.1.2 on page 11-2.");


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_WDATA_STABLE
  // =====
  property AXI_ERRM_WDATA_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WDATA})) &
          `AXI_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(WDATA & WdataMask);
  endproperty
  axi_errm_wdata_stable: assert property (AXI_ERRM_WDATA_STABLE) else
   $error("AXI_ERRM_WDATA_STABLE. WDATA must remain stable when WVALID is asserted and WREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_WID_STABLE
  // =====
  property AXI_ERRM_WID_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WID})) &
          `AXI_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(WID);
  endproperty
  axi_errm_wid_stable: assert property (AXI_ERRM_WID_STABLE) else
   $error("AXI_ERRM_WID_STABLE. WID must remain stable when WVALID is asserted and WREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_WLAST_STABLE
  // =====
  property AXI_ERRM_WLAST_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WLAST})) &
          `AXI_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(WLAST);
  endproperty
  axi_errm_wlast_stable: assert property (AXI_ERRM_WLAST_STABLE) else
   $error("AXI_ERRM_WLAST_STABLE. WLAST must remain stable when WVALID is asserted and WREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_WSTRB_STABLE
  // =====
  property AXI_ERRM_WSTRB_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WSTRB})) &
          `AXI_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(WSTRB);
  endproperty
  axi_errm_wstrb_stable: assert property (AXI_ERRM_WSTRB_STABLE) else
   $error("AXI_ERRM_WSTRB_STABLE. WSTRB must remain stable when WVALID is asserted and WREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_WVALID_STABLE
  // =====
  property AXI_ERRM_WVALID_STABLE;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & WVALID & !WREADY & !($isunknown({WVALID,WREADY}))
      ##1 `AXI_SVA_RSTn
      |-> WVALID;
  endproperty
  axi_errm_wvalid_stable: assert property (AXI_ERRM_WVALID_STABLE) else
   $error("AXI_ERRM_WVALID_STABLE. Once WVALID is asserted, it must remain asserted until WREADY is high. Spec: section 3.1.2 on page 3-4.");


  // INDEX:        - AXI_RECS_WREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI_RECS_WREADY_MAX_WAIT;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown({WVALID,WREADY})) &
      i_RecommendOn                            & // Parameter that can disable all AXI_REC*_* rules
      i_RecMaxWaitOn                           & // Parameter that can disable just AXI_REC*_MAX_WAIT rules
                         ( WVALID & !WREADY) 
      |-> ##[1:MAXWAITS] (!WVALID |  WREADY);  // READY=1 within MAXWAITS cycles (or VALID=0)
  endproperty
  axi_recs_wready_max_wait: assert property (AXI_RECS_WREADY_MAX_WAIT) else
   $warning("AXI_RECS_WREADY_MAX_WAIT. WREADY should be asserted within MAXWAITS cycles of WVALID being asserted.");  


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRM_WDATA_X
  // =====
  property AXI_ERRM_WDATA_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & WVALID & !($isunknown(WdataMask))
        |-> ! $isunknown(WDATA & WdataMask);
  endproperty
  axi_errm_wdata_x: assert property (AXI_ERRM_WDATA_X) else
   $error("AXI_ERRM_WDATA_X. When WVALID is high, a value of X on active byte lanes of WDATA is not permitted.");


  // INDEX:        - AXI_ERRM_WID_X
  // =====
  property AXI_ERRM_WID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & WVALID
        |-> ! $isunknown(WID);
  endproperty
  axi_errm_wid_x: assert property (AXI_ERRM_WID_X) else
   $error("AXI_ERRM_WID_X. When WVALID is high, a value of X on WID is not permitted. Spec: section 3.1.2 on page 3-4.");


  // INDEX:        - AXI_ERRM_WLAST_X
  // =====
  property AXI_ERRM_WLAST_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & WVALID
        |-> ! $isunknown(WLAST);
  endproperty
  axi_errm_wlast_x: assert property (AXI_ERRM_WLAST_X) else
   $error("AXI_ERRM_WLAST_X. When WVALID is high, a value of X on WLAST is not permitted.");


  // INDEX:        - AXI_ERRM_WSTRB_X
  // =====
  property AXI_ERRM_WSTRB_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & WVALID
        |-> ! $isunknown(WSTRB);
  endproperty
  axi_errm_wstrb_x: assert property (AXI_ERRM_WSTRB_X) else
   $error("AXI_ERRM_WSTRB_X. When WVALID is high, a value of X on WSTRB is not permitted.");


  // INDEX:        - AXI_ERRM_WVALID_X
  // =====
  property AXI_ERRM_WVALID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(WVALID);
  endproperty
  axi_errm_wvalid_x: assert property (AXI_ERRM_WVALID_X) else
   $error("AXI_ERRM_WVALID_X. When not in reset, a value of X on WVALID is not permitted.");


  // INDEX:        - AXI_ERRS_WREADY_X
  // =====
  property AXI_ERRS_WREADY_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(WREADY);
  endproperty
  axi_errs_wready_x: assert property (AXI_ERRS_WREADY_X) else
   $error("AXI_ERRS_WREADY_X. When not in reset, a value of X on WREADY is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Write Response Channel (*_B*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRS_BRESP
  // =====
  property AXI_ERRS_BRESP;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(BrespError))
      |-> ~BrespError;
  endproperty
  axi_errs_bresp: assert property (AXI_ERRS_BRESP) else
   $error("AXI_ERRS_BRESP. A slave must only give a write response after the last write data item is transferred. Spec: section 3.3 on page 3-7, and figure 3-5 on page 3-8.");


  // INDEX:        - AXI_ERRS_BRESP_ALL_DONE_EOS
  // =====
  // EOS: End-Of-Simulation check (not suitable for formal proofs).
  // Use +define+AXI_END_OF_SIMULATION=tb.EOS_signal when compiling.
`ifdef AXI_END_OF_SIMULATION
  property AXI_ERRS_BRESP_ALL_DONE_EOS;
    @(posedge `AXI_SVA_CLK)
          !($isunknown(`AXI_END_OF_SIMULATION)) &
          `AXI_SVA_RSTn
      ##1 `AXI_SVA_RSTn & $rose(`AXI_END_OF_SIMULATION)
      |-> (WIndex == 1);
  endproperty
  axi_errs_bresp_all_done_eos: assert property (AXI_ERRS_BRESP_ALL_DONE_EOS) else
   $error("AXI_ERRS_BRESP_ALL_DONE_EOS. All write transaction addresses must have been matched with corresponding write response.");
`endif


  // INDEX:        - AXI_ERRS_BRESP_EXOKAY
  // =====
  property AXI_ERRS_BRESP_EXOKAY;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(BrespExokError))
      |-> ~BrespExokError;
  endproperty
  axi_errs_bresp_exokay: assert property (AXI_ERRS_BRESP_EXOKAY) else
   $error("AXI_ERRS_BRESP_EXOKAY. An EXOKAY write response can only be given to an exclusive write access. Spec: section 6.2.3 on page 6-4.");


  // INDEX:        - AXI_ERRS_BVALID_RESET
  // =====
  property AXI_ERRS_BVALID_RESET;
    @(posedge `AXI_SVA_CLK)
          !(`AXI_SVA_RSTn) & !($isunknown(`AXI_SVA_RSTn))
      ##1  `AXI_SVA_RSTn
      |-> !BVALID;
  endproperty
  axi_errs_bvalid_reset: assert property (AXI_ERRS_BVALID_RESET) else
   $error("AXI_ERRS_BVALID_RESET. BVALID must be low in the cycle when ARESETn first goes high. Spec: section 11.1.2 on page 11-2.");


  // INDEX:        - AXI_RECS_BRESP 
  // =====
  property AXI_RECS_BRESP;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & !($isunknown(BrespLeadingRec)) &
          i_RecommendOn
      |-> ~BrespLeadingRec;
  endproperty
  axi_recs_bresp: assert property (AXI_RECS_BRESP) else
   $error("AXI_RECS_BRESP. A slave should not give a write response before the write address. ARM FAQs: 11424");


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRS_BID_STABLE
  // =====
  property AXI_ERRS_BID_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({BVALID,BREADY,BID})) &
          `AXI_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(BID);
  endproperty
  axi_errs_bid_stable: assert property (AXI_ERRS_BID_STABLE) else
   $error("AXI_ERRS_BID_STABLE. BID must remain stable when BVALID is asserted and BREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_BRESP_STABLE
  // =====
  property AXI_ERRS_BRESP_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({BVALID,BREADY,BRESP})) &
          `AXI_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(BRESP);
  endproperty
  axi_errs_bresp_stable: assert property (AXI_ERRS_BRESP_STABLE) else
   $error("AXI_ERRS_BRESP_STABLE. BRESP must remain stable when BVALID is asserted and BREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_BVALID_STABLE
  // =====
  property AXI_ERRS_BVALID_STABLE;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & BVALID & !BREADY & !($isunknown({BVALID,BREADY}))
      ##1 `AXI_SVA_RSTn
      |-> BVALID;
  endproperty
  axi_errs_bvalid_stable: assert property (AXI_ERRS_BVALID_STABLE) else
   $error("AXI_ERRS_BVALID_STABLE. Once BVALID is asserted, it must remain asserted until BREADY is high. Spec: section 3.1.3 on page 3-4.");


  // INDEX:        - AXI_RECM_BREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI_RECM_BREADY_MAX_WAIT;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown({BVALID,BREADY})) &
      i_RecommendOn                            & // Parameter that can disable all AXI_REC*_* rules
      i_RecMaxWaitOn                           & // Parameter that can disable just AXI_REC*_MAX_WAIT rules
                         ( BVALID & !BREADY) 
      |-> ##[1:MAXWAITS] (!BVALID |  BREADY);  // READY=1 within MAXWAITS cycles (or VALID=0)
  endproperty
  axi_recm_bready_max_wait: assert property (AXI_RECM_BREADY_MAX_WAIT) else
   $warning("AXI_RECM_BREADY_MAX_WAIT. BREADY should be asserted within MAXWAITS cycles of BVALID being asserted.");


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRM_BREADY_X
  // =====
  property AXI_ERRM_BREADY_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(BREADY);
  endproperty
  axi_errm_bready_x: assert property (AXI_ERRM_BREADY_X) else
   $error("AXI_ERRM_BREADY_X. When not in reset, a value of X on BREADY is not permitted.");


  // INDEX:        - AXI_ERRS_BID_X
  // =====
  property AXI_ERRS_BID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & BVALID
        |-> ! $isunknown(BID);
  endproperty
  axi_errs_bid_x: assert property (AXI_ERRS_BID_X) else
   $error("AXI_ERRS_BID_X. When BVALID is high, a value of X on BID is not permitted.");


  // INDEX:        - AXI_ERRS_BRESP_X
  // =====
  property AXI_ERRS_BRESP_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & BVALID
        |-> ! $isunknown(BRESP);
  endproperty
  axi_errs_bresp_x: assert property (AXI_ERRS_BRESP_X) else
   $error("AXI_ERRS_BRESP_X. When BVALID is high, a value of X on BRESP is not permitted.  Spec: section 3.1.3 on page 3-4.");


  // INDEX:        - AXI_ERRS_BVALID_X
  // =====
  property AXI_ERRS_BVALID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(BVALID);
  endproperty
  axi_errs_bvalid_x: assert property (AXI_ERRS_BVALID_X) else
   $error("AXI_ERRS_BVALID_X. When not in reset, a value of X on BVALID is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Read Address Channel (*_AR*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_ARADDR_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  //
  // Only need to check INCR bursts since:
  //
  //   a) FIXED bursts cannot violate the 4kB boundary by definition
  //
  //   b) WRAP bursts always stay within a <4kB region because of the wrap
  //      address boundary.  The biggest WRAP burst possible has length 16,
  //      size 128 bytes (1024 bits), so it can transfer 2048 bytes. The
  //      individual transfer addresses wrap at a 2048 byte address boundary,
  //      and the max data transferred in also 2048 bytes, so a 4kB boundary
  //      can never be broken.
  property AXI_ERRM_ARADDR_BOUNDARY;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARBURST,ARADDR})) &
          ARVALID & (ARBURST == `AXI_ABURST_INCR)
      |-> (ArAddrIncr[ADDR_MAX:12] == ARADDR[ADDR_MAX:12]);
  endproperty
  axi_errm_araddr_boundary: assert property (AXI_ERRM_ARADDR_BOUNDARY) else
   $error("AXI_ERRM_ARADDR_BOUNDARY. A read burst cannot cross a 4kbyte boundary. Spec: section 4.1 on page 4-2.");


  // INDEX:        - AXI_ERRM_ARADDR_WRAP_ALIGN
  // =====
  property AXI_ERRM_ARADDR_WRAP_ALIGN;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARBURST,ARADDR})) &
          ARVALID & (ARBURST == `AXI_ABURST_WRAP)
      |-> ((ARADDR[6:0] & AlignMaskR) == ARADDR[6:0]);
  endproperty
  axi_errm_araddr_wrap_align: assert property (AXI_ERRM_ARADDR_WRAP_ALIGN) else
   $error("AXI_ERRM_ARADDR_WRAP_ALIGN. A read transaction with burst type WRAP must have an aligned address. Spec: section 4.4.3 on page 4-6.");


  // INDEX:        - AXI_ERRM_ARBURST
  // =====
  property AXI_ERRM_ARBURST;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARBURST})) &
          ARVALID
      |-> (ARBURST != 2'b11);
  endproperty
  axi_errm_arburst: assert property (AXI_ERRM_ARBURST) else
   $error("AXI_ERRM_ARBURST. When ARVALID is high, a value of 2'b11 on ARBURST is not permitted. Spec: table 4-3 on page 4-5.");


  // INDEX:        - AXI_ERRM_ARCACHE
  // =====
  property AXI_ERRM_ARCACHE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARCACHE})) &
          ARVALID & ~ARCACHE[1]
      |-> (ARCACHE[3:2] == 2'b00);
  endproperty
  axi_errm_arcache: assert property (AXI_ERRM_ARCACHE) else
   $error("AXI_ERRM_ARCACHE. When ARVALID is high, if ARCACHE[1] is low then ARCACHE[3] and ARCACHE[2] must also be low. Spec: table 5-1 on page 5-3.");


  // INDEX:        - AXI_ERRM_ARLEN_WRAP
  // =====
  property AXI_ERRM_ARLEN_WRAP;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARBURST,ARLEN})) &
          ARVALID & (ARBURST == `AXI_ABURST_WRAP)
      |-> (ARLEN == `AXI_ALEN_2 ||
           ARLEN == `AXI_ALEN_4 ||
           ARLEN == `AXI_ALEN_8 ||
           ARLEN == `AXI_ALEN_16);
  endproperty
  axi_errm_arlen_wrap: assert property (AXI_ERRM_ARLEN_WRAP) else
   $error("AXI_ERRM_ARLEN_WRAP. A read transaction with burst type WRAP must have length 2, 4, 8 or 16. Spec: section 4.4.3 on page 4-6.");


  // INDEX:        - AXI_ERRM_ARLOCK
  // =====
  property AXI_ERRM_ARLOCK;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARLOCK})) &
          ARVALID
      |-> (ARLOCK != 2'b11);
  endproperty
  axi_errm_arlock: assert property (AXI_ERRM_ARLOCK) else
   $error("AXI_ERRM_ARLOCK. When ARVALID is high, a value of 2'b11 on ARLOCK is not permitted. Spec: table 6-1 on page 6-2.");


  // INDEX:        - AXI_ERRM_ARLOCK_END
  // =====
  property AXI_ERRM_ARLOCK_END;
    @(posedge `AXI_SVA_CLK)
          (LockState == `AXI_AUX_ST_LOCK_LAST) & // the unlocking transfer has begun and should have completed
          ARNew                                  // new valid read address
      |-> nROutstanding &                        // no outstanding reads
          nWAddrTrans &                          // no writes other than leading write data (checked separately)
          !FlagLLInWCam;                         // no leading write transactions from previous lock last period
  endproperty
  axi_errm_arlock_end: assert property (AXI_ERRM_ARLOCK_END) else
   $error("AXI_ERRM_ARLOCK_END. A master must wait for an unlocked transaction at the end of a locked sequence to complete before issuing another read transaction. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_ARLOCK_ID
  // =====
  property AXI_ERRM_ARLOCK_ID;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWID,AWLOCK,
                        ARID,ARLOCK}))
      |->
          // case for in lock or going into lock last
          !(ARNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid read address in a locked sequence
           (ARID != LockId)                               // id value does not match current lock id
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&      // in unlocked or lock last state
           (AWID != ARID)                                 // lock id values do not agree
          );
  endproperty
  axi_errm_arlock_id: assert property (AXI_ERRM_ARLOCK_ID) else
   $error("AXI_ERRM_ARLOCK_ID. A sequence of locked transactions must use a single ID. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_ARLOCK_LAST
  // =====
  property AXI_ERRM_ARLOCK_LAST;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,WVALID})) &
          ARLockLastNew        // going into lock last with a locked read
      |-> nROutstanding &      // no outstanding reads
          (WIndex == 1) &      // no writes (including leading write data)
          ~AWVALID & ~WVALID & // no activity on write channels
          !FlagLOInWCam;       // no leading write transactions from previous locked period
  endproperty
  axi_errm_arlock_last: assert property (AXI_ERRM_ARLOCK_LAST) else
   $error("AXI_ERRM_ARLOCK_LAST. A master must wait for all locked transactions to complete before issuing an unlocking read transaction. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_ARLOCK_START
  // =====
  property AXI_ERRM_ARLOCK_START;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWLOCK})) &
          ARLockNew                                    // going into locked with a locked read
      |-> nROutstanding &                              // no outstanding reads
          nWAddrTrans &                                // no writes other than leading write data (checked separately)
          !(AWVALID & (AWLOCK != `AXI_ALOCK_LOCKED)) & // allow a new write but only if it is locked
          !FlagUNInWCam &                              // no leading write transactions from previous unlocked period
          !FlagLLInWCam;                               // no leading write transactions from previous lock last period
  endproperty
  axi_errm_arlock_start: assert property (AXI_ERRM_ARLOCK_START) else
   $error("AXI_ERRM_ARLOCK_START. A master must wait for all outstanding transactions to complete before issuing a read transaction which is the first in a locked sequence. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_ERRM_ARSIZE
  // =====
  property AXI_ERRM_ARSIZE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARSIZE})) &
          ARVALID
      |-> (ArSizeInBits <= DATA_WIDTH);
  endproperty
  axi_errm_arsize: assert property (AXI_ERRM_ARSIZE) else
   $error("AXI_ERRM_ARSIZE. The size of a read transfer must not exceed the width of the data port. Spec: section 4.3 on page 4-4.");


  // INDEX:        - AXI_ERRM_ARVALID_RESET
  // =====
  property AXI_ERRM_ARVALID_RESET;
    @(posedge `AXI_SVA_CLK)
          !(`AXI_SVA_RSTn) & !($isunknown(`AXI_SVA_RSTn))
      ##1  `AXI_SVA_RSTn
      |-> !ARVALID;
  endproperty
  axi_errm_arvalid_reset: assert property (AXI_ERRM_ARVALID_RESET) else
   $error("AXI_ERRM_ARVALID_RESET. ARVALID must be low in the cycle when ARESETn first goes high. Spec: section 11.1.2 on page 11-2.");


  // INDEX:        - AXI_RECM_ARLOCK_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  property AXI_RECM_ARLOCK_BOUNDARY;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWADDR,AWLOCK,
                        ARADDR,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(ARNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid read address in a locked sequence
           (ARADDR[ADDR_MAX:12] != LockAddr[ADDR_MAX:12]) // address does not match current lock region
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&      // in unlocked or lock last state
           (AWADDR[ADDR_MAX:12] != ARADDR[ADDR_MAX:12])   // lock address region values do not agree
          );
  endproperty
  axi_recm_arlock_boundary: assert property (AXI_RECM_ARLOCK_BOUNDARY) else
   $warning("AXI_RECM_ARLOCK_BOUNDARY. It is recommended that all locked transaction sequences are kept within the same 4KB address region. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_RECM_ARLOCK_CTRL
  // =====
  property AXI_RECM_ARLOCK_CTRL;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWPROT,AWCACHE,AWLOCK,
                        ARPROT,ARCACHE,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(ARNew && (LockState == `AXI_AUX_ST_LOCKED) &&   // new valid read address in a locked sequence
           ((ARPROT != LockProt) || (ARCACHE != LockCache)) // PROT or CACHE values do not match current lock
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&       // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&        // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST)) &&        // in unlocked or lock last state
           ((AWPROT != ARPROT) || (AWCACHE != ARCACHE))     // lock PROT or CACHE values do not agree
          );
  endproperty
  axi_recm_arlock_ctrl: assert property (AXI_RECM_ARLOCK_CTRL) else
   $warning("AXI_RECM_ARLOCK_CTRL. It is recommended that a master should not change AxPROT or AxCACHE during a sequence of locked accesses. Spec: section 6.3 on page 6-7.");


  // INDEX:        - AXI_RECM_ARLOCK_NUM
  // =====
  property AXI_RECM_ARLOCK_NUM;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWLOCK,ARLOCK})) &
          i_RecommendOn                        // Parameter that can disable all AXI_REC*_* rules
      |->
          // case for in lock or going into lock last
          !(ARNew && (LockState == `AXI_AUX_ST_LOCKED) && // new valid read address in a locked sequence
           (ARLOCK == `AXI_ALOCK_LOCKED)                  // read is locked
          ) &&
          // case for going into lock from either unlocked or lock last with both a locked read and write
          !(AWNew && (AWLOCK == `AXI_ALOCK_LOCKED) &&     // new valid locked write
           ARNew && (ARLOCK == `AXI_ALOCK_LOCKED) &&      // new valid locked read
           ((LockState == `AXI_AUX_ST_UNLOCKED) ||
            (LockState == `AXI_AUX_ST_LOCK_LAST))         // in unlocked or lock last state
          );
  endproperty
  axi_recm_arlock_num: assert property (AXI_RECM_ARLOCK_NUM) else
   $warning("AXI_RECM_ARLOCK_NUM. It is recommended that locked transaction sequences are limited to two transactions. Spec: section 6.3 on page 6-7.");


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_ARADDR_STABLE
  // =====
  property AXI_ERRM_ARADDR_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARADDR})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARADDR);
  endproperty
  axi_errm_araddr_stable: assert property (AXI_ERRM_ARADDR_STABLE) else
   $error("AXI_ERRM_ARADDR_STABLE. ARADDR must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARBURST_STABLE
  // =====
  property AXI_ERRM_ARBURST_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARBURST})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARBURST);
  endproperty
  axi_errm_arburst_stable: assert property (AXI_ERRM_ARBURST_STABLE) else
   $error("AXI_ERRM_ARBURST_STABLE. ARBURST must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARCACHE_STABLE
  // =====
  property AXI_ERRM_ARCACHE_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARCACHE})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARCACHE);
  endproperty
  axi_errm_arcache_stable: assert property (AXI_ERRM_ARCACHE_STABLE) else
   $error("AXI_ERRM_ARCACHE_STABLE. ARCACHE must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARID_STABLE
  // =====
  property AXI_ERRM_ARID_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARID})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARID);
  endproperty
  axi_errm_arid_stable: assert property (AXI_ERRM_ARID_STABLE) else
   $error("AXI_ERRM_ARID_STABLE. ARID must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARLEN_STABLE
  // =====
  property AXI_ERRM_ARLEN_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARLEN})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARLEN);
  endproperty
  axi_errm_arlen_stable: assert property (AXI_ERRM_ARLEN_STABLE) else
   $error("AXI_ERRM_ARLEN_STABLE. ARLEN must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARLOCK_STABLE
  // =====
  property AXI_ERRM_ARLOCK_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARLOCK})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARLOCK);
  endproperty
  axi_errm_arlock_stable: assert property (AXI_ERRM_ARLOCK_STABLE) else
   $error("AXI_ERRM_ARLOCK_STABLE. ARLOCK must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARPROT_STABLE
  // =====
  property AXI_ERRM_ARPROT_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARPROT})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARPROT);
  endproperty
  axi_errm_arprot_stable: assert property (AXI_ERRM_ARPROT_STABLE) else
   $error("AXI_ERRM_ARPROT_STABLE. ARPROT must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARSIZE_STABLE
  // =====
  property AXI_ERRM_ARSIZE_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARSIZE})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARSIZE);
  endproperty
  axi_errm_arsize_stable: assert property (AXI_ERRM_ARSIZE_STABLE) else
   $error("AXI_ERRM_ARSIZE_STABLE. ARSIZE must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARVALID_STABLE
  // =====
  property AXI_ERRM_ARVALID_STABLE;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & ARVALID & !ARREADY & !($isunknown({ARVALID,ARREADY}))
      ##1 `AXI_SVA_RSTn
      |-> ARVALID;
  endproperty
  axi_errm_arvalid_stable: assert property (AXI_ERRM_ARVALID_STABLE) else
   $error("AXI_ERRM_ARVALID_STABLE. Once ARVALID is asserted, it must remain asserted until ARREADY is high. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_RECS_ARREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI_RECS_ARREADY_MAX_WAIT;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown({ARVALID,ARREADY})) &
      i_RecommendOn                            & // Parameter that can disable all AXI_REC*_* rules
      i_RecMaxWaitOn                           & // Parameter that can disable just AXI_REC*_MAX_WAIT rules
                         ( ARVALID & !ARREADY) 
      |-> ##[1:MAXWAITS] (!ARVALID |  ARREADY);  // READY=1 within MAXWAITS cycles (or VALID=0)
  endproperty
  axi_recs_arready_max_wait: assert property (AXI_RECS_ARREADY_MAX_WAIT) else
   $warning("AXI_RECS_ARREADY_MAX_WAIT. ARREADY should be asserted within MAXWAITS cycles of ARVALID being asserted.");  


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRM_ARADDR_X
  // =====
  property AXI_ERRM_ARADDR_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARADDR);
  endproperty
  axi_errm_araddr_x: assert property (AXI_ERRM_ARADDR_X) else
   $error("AXI_ERRM_ARADDR_X. When ARVALID is high, a value of X on ARADDR is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARBURST_X
  // =====
  property AXI_ERRM_ARBURST_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARBURST);
  endproperty
  axi_errm_arburst_x: assert property (AXI_ERRM_ARBURST_X) else
   $error("AXI_ERRM_ARBURST_X. When ARVALID is high, a value of X on ARBURST is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARCACHE_X
  // =====
  property AXI_ERRM_ARCACHE_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARCACHE);
  endproperty
  axi_errm_arcache_x: assert property (AXI_ERRM_ARCACHE_X) else
   $error("AXI_ERRM_ARCACHE_X. When ARVALID is high, a value of X on ARCACHE is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARID_X
  // =====
  property AXI_ERRM_ARID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARID);
  endproperty
  axi_errm_arid_x: assert property (AXI_ERRM_ARID_X) else
   $error("AXI_ERRM_ARID_X. When ARVALID is high, a value of X on ARID is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARLEN_X
  // =====
  property AXI_ERRM_ARLEN_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARLEN);
  endproperty
  axi_errm_arlen_x: assert property (AXI_ERRM_ARLEN_X) else
   $error("AXI_ERRM_ARLEN_X. When ARVALID is high, a value of X on ARLEN is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARLOCK_X
  // =====
  property AXI_ERRM_ARLOCK_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARLOCK);
  endproperty
  axi_errm_arlock_x: assert property (AXI_ERRM_ARLOCK_X) else
   $error("AXI_ERRM_ARLOCK_X. When ARVALID is high, a value of X on ARLOCK is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARPROT_X
  // =====
  property AXI_ERRM_ARPROT_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARPROT);
  endproperty
  axi_errm_arprot_x: assert property (AXI_ERRM_ARPROT_X) else
   $error("AXI_ERRM_ARPROT_X. When ARVALID is high, a value of X on ARPROT is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARSIZE_X
  // =====
  property AXI_ERRM_ARSIZE_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARSIZE);
  endproperty
  axi_errm_arsize_x: assert property (AXI_ERRM_ARSIZE_X) else
   $error("AXI_ERRM_ARSIZE_X. When ARVALID is high, a value of X on ARSIZE is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRM_ARVALID_X
  // =====
  property AXI_ERRM_ARVALID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(ARVALID);
  endproperty
  axi_errm_arvalid_x: assert property (AXI_ERRM_ARVALID_X) else
   $error("AXI_ERRM_ARVALID_X. When not in reset, a value of X on ARVALID is not permitted.");


  // INDEX:        - AXI_ERRS_ARREADY_X
  // =====
  property AXI_ERRS_ARREADY_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(ARREADY);
  endproperty
  axi_errs_arready_x: assert property (AXI_ERRS_ARREADY_X) else
   $error("AXI_ERRS_ARREADY_X. When not in reset, a value of X on ARREADY is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Read Data Channel (*_R*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRS_RDATA_NUM
  // =====
  property AXI_ERRS_RDATA_NUM;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RLAST,ArLenPending})) &
          RVALID & RREADY
      |-> ( ((ArCountPending == ArLenPending) & RLAST)  //     Last RDATA and RLAST is     asserted
           |((ArCountPending != ArLenPending) & ~RLAST) // Not last RDATA and RLAST is not asserted
          );
  endproperty
  axi_errs_rdata_num: assert property (AXI_ERRS_RDATA_NUM) else
   $error("AXI_ERRS_RDATA_NUM. The number of read data items must match the corresponding ARLEN. Spec: table 4-1 on page 4-3.");


  // INDEX:        - AXI_ERRS_RLAST_ALL_DONE_EOS
  // =====
  // EOS: End-Of-Simulation check (not suitable for formal proofs).
  // Use +define+AXI_END_OF_SIMULATION=tb.EOS_signal when compiling.
`ifdef AXI_END_OF_SIMULATION
  property AXI_ERRS_RLAST_ALL_DONE_EOS;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({`AXI_END_OF_SIMULATION,nROutstanding})) &
          `AXI_SVA_RSTn
      ##1 `AXI_SVA_RSTn & $rose(`AXI_END_OF_SIMULATION)
      |-> (nROutstanding == 1'b1);
  endproperty
  axi_errs_rlast_all_done_eos: assert property (AXI_ERRS_RLAST_ALL_DONE_EOS) else
   $error("AXI_ERRS_RLAST_ALL_DONE_EOS. All outstanding read bursts must have completed.");
`endif


  // INDEX:        - AXI_ERRS_RID
  // =====
  // Read data must always follow the address that it relates to.
  property AXI_ERRS_RID;
    @(posedge `AXI_SVA_CLK)
          !($isunknown(RVALID)) &
          RVALID
      |-> (RidMatch > 0);
  endproperty
  axi_errs_rid: assert property (AXI_ERRS_RID) else
   $error("AXI_ERRS_RID. A slave can only give read data with an ID to match an outstanding read transaction. Spec: section 8.3 on page 8-4.");


  // INDEX:        - AXI_ERRS_RRESP_EXOKAY
  // =====
  property AXI_ERRS_RRESP_EXOKAY;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RRESP})) &
          RVALID & RREADY & (RRESP == `AXI_RESP_EXOKAY)
      |-> (ArExclPending);
  endproperty
  axi_errs_rresp_exokay: assert property (AXI_ERRS_RRESP_EXOKAY) else
   $error("AXI_ERRS_RRESP_EXOKAY. An EXOKAY read response can only be given to an exclusive read access. Spec: section 6.2.3 on page 6-4.");


  // INDEX:        - AXI_ERRS_RVALID_RESET
  // =====
  property AXI_ERRS_RVALID_RESET;
    @(posedge `AXI_SVA_CLK)
          !(`AXI_SVA_RSTn) & !($isunknown(`AXI_SVA_RSTn))
      ##1   `AXI_SVA_RSTn
      |-> !RVALID;
  endproperty
   axi_errs_rvalid_reset: assert property (AXI_ERRS_RVALID_RESET) else
   $error("AXI_ERRS_RVALID_RESET. RVALID must be low in the cycle when ARESETn first goes high. Spec: section 11.1.2 on page 11-2.");


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRS_RDATA_STABLE
  // =====
  property AXI_ERRS_RDATA_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RDATA})) &
          `AXI_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(RDATA
                    | ~RdataMask
                 );
  endproperty
  axi_errs_rdata_stable: assert property (AXI_ERRS_RDATA_STABLE) else
   $error("AXI_ERRS_RDATA_STABLE. RDATA must remain stable when RVALID is asserted and RREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_RID_STABLE
  // =====
  property AXI_ERRS_RID_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RID})) &
          `AXI_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(RID);
  endproperty
  axi_errs_rid_stable: assert property (AXI_ERRS_RID_STABLE) else
   $error("AXI_ERRS_RID_STABLE. RID must remain stable when RVALID is asserted and RREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_RLAST_STABLE
  // =====
  property AXI_ERRS_RLAST_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RLAST})) &
          `AXI_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(RLAST);
  endproperty
  axi_errs_rlast_stable: assert property (AXI_ERRS_RLAST_STABLE) else
   $error("AXI_ERRS_RLAST_STABLE. RLAST must remain stable when RVALID is asserted and RREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_RRESP_STABLE
  // =====
  property AXI_ERRS_RRESP_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RRESP})) &
          `AXI_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(RRESP);
  endproperty
  axi_errs_rresp_stable: assert property (AXI_ERRS_RRESP_STABLE) else
   $error("AXI_ERRS_RRESP_STABLE. RRESP must remain stable when RVALID is asserted and RREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_RVALID_STABLE
  // =====
  property AXI_ERRS_RVALID_STABLE;
    @(posedge `AXI_SVA_CLK)
          `AXI_SVA_RSTn & RVALID & !RREADY & !($isunknown({RVALID,RREADY}))
      ##1 `AXI_SVA_RSTn
      |-> RVALID;
  endproperty
  axi_errs_rvalid_stable: assert property (AXI_ERRS_RVALID_STABLE) else
   $error("AXI_ERRS_RVALID_STABLE. Once RVALID is asserted, it must remain asserted until RREADY is high. Spec: section 3.1.5 on page 3-5.");


  // INDEX:        - AXI_RECM_RREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI_RECM_RREADY_MAX_WAIT;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown({RVALID,RREADY})) &
      i_RecommendOn                            & // Parameter that can disable all AXI_REC*_* rules
      i_RecMaxWaitOn                           & // Parameter that can disable just AXI_REC*_MAX_WAIT rules
                         ( RVALID & !RREADY) 
      |-> ##[1:MAXWAITS] (!RVALID |  RREADY);  // READY=1 within MAXWAITS cycles (or VALID=0)
  endproperty
  axi_recm_rready_max_wait: assert property (AXI_RECM_RREADY_MAX_WAIT) else
   $warning("AXI_RECM_RREADY_MAX_WAIT. RREADY should be asserted within MAXWAITS cycles of RVALID being asserted.");  


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRS_RDATA_X
  // =====
  property AXI_ERRS_RDATA_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & RVALID
        |-> ! $isunknown(RDATA | ~RdataMask);
  endproperty
  axi_errs_rdata_x: assert property (AXI_ERRS_RDATA_X) else
    $error("AXI_ERRS_RDATA_X. When RVALID is high, a value of X on RDATA valid byte lanes is not permitted.");


  // INDEX:        - AXI_ERRM_RREADY_X
  // =====
  property AXI_ERRM_RREADY_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(RREADY);
  endproperty
  axi_errm_rready_x: assert property (AXI_ERRM_RREADY_X) else
   $error("AXI_ERRM_RREADY_X. When not in reset, a value of X on RREADY is not permitted.");


  // INDEX:        - AXI_ERRS_RID_X
  // =====
  property AXI_ERRS_RID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & RVALID
        |-> ! $isunknown(RID);
  endproperty
  axi_errs_rid_x: assert property (AXI_ERRS_RID_X) else
    $error("AXI_ERRS_RID_X. When RVALID is high, a value of X on RID is not permitted.");


  // INDEX:        - AXI_ERRS_RLAST_X
  // =====
  property AXI_ERRS_RLAST_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & RVALID
        |-> ! $isunknown(RLAST);
  endproperty
  axi_errs_rlast_x: assert property (AXI_ERRS_RLAST_X) else
   $error("AXI_ERRS_RLAST_X. When RVALID is high, a value of X on RLAST is not permitted.");


  // INDEX:        - AXI_ERRS_RRESP_X
  // =====
  property AXI_ERRS_RRESP_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & RVALID
        |-> ! $isunknown(RRESP);
  endproperty
  axi_errs_rresp_x: assert property (AXI_ERRS_RRESP_X) else
   $error("AXI_ERRS_RRESP_X. When RVALID is high, a value of X on RRESP is not permitted.");


  // INDEX:        - AXI_ERRS_RVALID_X
  // =====
  property AXI_ERRS_RVALID_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(RVALID);
  endproperty
  axi_errs_rvalid_x: assert property (AXI_ERRS_RVALID_X) else
   $error("AXI_ERRS_RVALID_X. When not in reset, a value of X on RVALID is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Low Power Interface (*_C*)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules (none for Low Power signals)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules (asynchronous to ACLK)
// =====
// The low-power handshake rules below use rising/falling edges on REQ and ACK,
// in order to detect changes within ACLK cycles (including low power state).
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRL_CSYSACK_FALL
  // =====
  property AXI_ERRL_CSYSACK_FALL;
    @(negedge CSYSACK)                  // falling edge of CSYSACK
      `AXI_SVA_RSTn & !($isunknown(CSYSREQ))
      |-> ~CSYSREQ;                     // CSYSREQ low
  endproperty
  axi_errl_csysack_fall: assert property (AXI_ERRL_CSYSACK_FALL) else
   $error("AXI_ERRL_CSYSACK_FALL. When CSYSACK transitions from high to low, CSYSREQ must be low. Spec: figure 12-1 on page 12-3.");


  // INDEX:        - AXI_ERRL_CSYSACK_RISE
  // =====
  property AXI_ERRL_CSYSACK_RISE;
    @(posedge CSYSACK)                  // rising edge of CSYSACK
      `AXI_SVA_RSTn & !($isunknown(CSYSREQ))
      |-> CSYSREQ;                      // CSYSREQ high
  endproperty
  axi_errl_csysack_rise: assert property (AXI_ERRL_CSYSACK_RISE) else
   $error("AXI_ERRL_CSYSACK_RISE. When CSYSACK transitions from low to high, CSYSREQ must be high. Spec: figure 12-1 on page 12-3.");


  // INDEX:        - AXI_ERRL_CSYSREQ_FALL
  // =====
  property AXI_ERRL_CSYSREQ_FALL;
    @(negedge CSYSREQ)                  // falling edge of CSYSREQ
      `AXI_SVA_RSTn & !($isunknown(CSYSACK))
      |-> CSYSACK;                      // CSYSACK high
  endproperty
  axi_errl_csysreq_fall: assert property (AXI_ERRL_CSYSREQ_FALL) else
   $error("AXI_ERRL_CSYSREQ_FALL. When CSYSREQ transitions from high to low, CSYSACK must be high. Spec: figure 12-1 on page 12-3.");


  // INDEX:        - AXI_ERRL_CSYSREQ_RISE
  // =====
  property AXI_ERRL_CSYSREQ_RISE;
    @(posedge CSYSREQ)                  // rising edge of CSYSREQ
      `AXI_SVA_RSTn & !($isunknown(CSYSACK))
      |-> ~CSYSACK;                     // CSYSACK low
  endproperty
  axi_errl_csysreq_rise: assert property (AXI_ERRL_CSYSREQ_RISE) else
   $error("AXI_ERRL_CSYSREQ_RISE. When CSYSREQ transitions from low to high, CSYSACK must be low. Spec: figure 12-1 on page 12-3.");


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRL_CACTIVE_X
  // =====
  property AXI_ERRL_CACTIVE_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(CACTIVE);
  endproperty
  axi_errl_cactive_x: assert property (AXI_ERRL_CACTIVE_X) else
   $error("AXI_ERRL_CACTIVE_X. When not in reset, a value of X on CACTIVE is not permitted.");


  // INDEX:        - AXI_ERRL_CSYSACK_X
  // =====
  property AXI_ERRL_CSYSACK_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(CSYSACK);
  endproperty
  axi_errl_csysack_x: assert property (AXI_ERRL_CSYSACK_X) else
   $error("AXI_ERRL_CSYSACK_X. When not in reset, a value of X on CSYSACK is not permitted.");


  // INDEX:        - AXI_ERRL_CSYSREQ_X
  // =====
  property AXI_ERRL_CSYSREQ_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn
        |-> ! $isunknown(CSYSREQ);
  endproperty
  axi_errl_csysreq_x: assert property (AXI_ERRL_CSYSREQ_X) else
   $error("AXI_ERRL_CSYSREQ_X. When not in reset, a value of X on CSYSREQ is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Exclusive Access
// =====
// These are inter-channel rules.
// Supports one outstanding exclusive access per ID
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------
// INDEX:        -


  // INDEX:        - AXI_ERRM_EXCL_ALIGN
  // =====
  // Burst lengths that are not a power of two are not checked here, because
  // these will violate EXCLLEN. Checked for excl reads only as AXI_RECM_EXCL_PAIR
  // or AXI_RECM_EXCL_MATCH will fire if an excl write violates.
  property AXI_ERRM_EXCL_ALIGN;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARLOCK,ARLEN,ARADDR})) &
          (ARVALID &                       // valid address
           (ARLOCK == `AXI_ALOCK_EXCL) &   // exclusive transaction
           (ARLEN == `AXI_ALEN_1 ||        // length is power of 2
            ARLEN == `AXI_ALEN_2 ||
            ARLEN == `AXI_ALEN_4 ||
            ARLEN == `AXI_ALEN_8 ||
            ARLEN == `AXI_ALEN_16))
      |-> ((ARADDR[10:0] & ExclMask) == ARADDR[10:0]); // address aligned
  endproperty
  axi_errm_excl_align: assert property (AXI_ERRM_EXCL_ALIGN) else
   $error("AXI_ERRM_EXCL_ALIGN. The address of an exclusive access must be aligned to the total number of bytes in the transaction. Spec: section 6.2.4 on page 6-5.");


  // INDEX:        - AXI_ERRM_EXCL_LEN
  // =====
  // Checked for excl reads only as AXI_RECM_EXCL_PAIR or AXI_RECM_EXCL_MATCH will
  // fire if an excl write violates.
  property AXI_ERRM_EXCL_LEN;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARLOCK,ARLEN})) &
          ARVALID & (ARLOCK == `AXI_ALOCK_EXCL)
      |-> ((ARLEN == `AXI_ALEN_1)  ||
           (ARLEN == `AXI_ALEN_2)  ||
           (ARLEN == `AXI_ALEN_4)  ||
           (ARLEN == `AXI_ALEN_8)  ||
           (ARLEN == `AXI_ALEN_16));
  endproperty
  axi_errm_excl_len: assert property (AXI_ERRM_EXCL_LEN) else
   $error("AXI_ERRM_EXCL_LEN. The number of bytes to be transferred in an exclusive access burst must be a power of 2. Spec: section 6.2.4 on page 6-5.");


  // INDEX:        - AXI_RECM_EXCL_MATCH
  // =====
  // Recommendation as it can be affected by software, e.g. if a dummy STREX is used to clear any outstanding exclusive accesses.
  property   AXI_RECM_EXCL_MATCH;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWLOCK,ExclAwId,ExclAwMatch,AWADDR,AWSIZE,AWLEN,AWBURST,AWCACHE,AWPROT,AWUSER})) &
          i_RecommendOn &                                  // Parameter that can disable all AXI_REC*_* rules
          AWVALID & AWREADY &
          (AWLOCK == `AXI_ALOCK_EXCL) & ExclReadAddr[ExclAwId] // excl write & excl read outstanding
          & ExclAwMatch
      |-> ((ExclAddr[ExclAwId] == AWADDR) &
           (ExclSize[ExclAwId] == AWSIZE) &
           (ExclLen[ExclAwId]  == AWLEN)  &
           (ExclBurst[ExclAwId]== AWBURST)&
           (ExclCache[ExclAwId]== AWCACHE)&
           (ExclProt[ExclAwId] == AWPROT) &
           (ExclUser[ExclAwId] == AWUSER)
          );
  endproperty
  axi_recm_excl_match: assert property (AXI_RECM_EXCL_MATCH) else
   $warning("AXI_RECM_EXCL_MATCH. The address, size and length of an exclusive write should be the same as the preceding exclusive read with the same ID. Spec: section 6.2.4 on page 6-5.");


  // INDEX:        - AXI_ERRM_EXCL_MAX
  // =====
  // Burst lengths that are not a power of two are not checked here, because
  // these will violate EXCLLEN. Bursts of length 1 can never violate this
  // rule. Checked for excl reads only as AXI_RECM_EXCL_PAIR or AXI_RECM_EXCL_MATCH will
  // fire if an excl write violates.
  property AXI_ERRM_EXCL_MAX;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARLOCK,ARLEN})) &
          (ARVALID &                      // valid address
           (ARLOCK == `AXI_ALOCK_EXCL) &  // exclusive transaction
           (ARLEN == `AXI_ALEN_2 ||       // length is power of 2
            ARLEN == `AXI_ALEN_4 ||
            ARLEN == `AXI_ALEN_8 ||
            ARLEN == `AXI_ALEN_16))
      |-> (ArLenInBytes <= 128 );         // max 128 bytes transferred
  endproperty
  axi_errm_excl_max: assert property (AXI_ERRM_EXCL_MAX) else
   $error("AXI_ERRM_EXCL_MAX. The maximum number of bytes that can be transferred in an exclusive burst is 128. Spec: section 6.2.4 on page 6-5.");


  // INDEX:        - AXI_RECM_EXCL_PAIR
  // =====
  // Recommendation as it can be affected by software, e.g. if a dummy STREX is used to clear any outstanding exclusive accesses.
  property   AXI_RECM_EXCL_PAIR;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWLOCK,ExclAwMatch,ExclAwId})) &
          i_RecommendOn &                                 // Parameter that can disable all AXI_REC*_* rules
          AWVALID & AWREADY & (AWLOCK == `AXI_ALOCK_EXCL) // excl write
      |-> (ExclAwMatch &&
           ExclReadAddr[ExclAwId] &&
           ExclReadData[ExclAwId]);                       // excl read with same ID complete
  endproperty
  axi_recm_excl_pair: assert property (AXI_RECM_EXCL_PAIR) else
   $warning("AXI_RECM_EXCL_PAIR. An exclusive write should have an earlier outstanding completed exclusive read with the same ID. Spec: section 6.2.2 on page 6-4.");


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: USER_* Rules (extension to AXI)
// =====
// The USER signals are user-defined extensions to the AXI spec, so have been
// located separately from the channel-specific rules.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules (none for USER signals)
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI_ERRM_AWUSER_STABLE
  // =====
  property AXI_ERRM_AWUSER_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({AWVALID,AWREADY,AWUSER})) &
          `AXI_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(AWUSER);
  endproperty
  axi_errm_awuser_stable: assert property (AXI_ERRM_AWUSER_STABLE) else
   $error("AXI_ERRM_AWUSER_STABLE. AWUSER must remain stable when AWVALID is asserted and AWREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_WUSER_STABLE
  // =====
  property AXI_ERRM_WUSER_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({WVALID,WREADY,WUSER})) &
          `AXI_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(WUSER);
  endproperty
  axi_errm_wuser_stable: assert property (AXI_ERRM_WUSER_STABLE) else
   $error("AXI_ERRM_WUSER_STABLE. WUSER must remain stable when WVALID is asserted and WREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_BUSER_STABLE
  // =====
  property AXI_ERRS_BUSER_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({BVALID,BREADY,BUSER})) &
          `AXI_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(BUSER);
  endproperty
  axi_errs_buser_stable: assert property (AXI_ERRS_BUSER_STABLE) else
   $error("AXI_ERRS_BUSER_STABLE. BUSER must remain stable when BVALID is asserted and BREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRM_ARUSER_STABLE
  // =====
  property AXI_ERRM_ARUSER_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({ARVALID,ARREADY,ARUSER})) &
          `AXI_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(ARUSER);
  endproperty
  axi_errm_aruser_stable: assert property (AXI_ERRM_ARUSER_STABLE) else
   $error("AXI_ERRM_ARUSER_STABLE. ARUSER must remain stable when ARVALID is asserted and ARREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


  // INDEX:        - AXI_ERRS_RUSER_STABLE
  // =====
  property AXI_ERRS_RUSER_STABLE;
    @(posedge `AXI_SVA_CLK)
          !($isunknown({RVALID,RREADY,RUSER})) &
          `AXI_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI_SVA_RSTn
      |-> $stable(RUSER);
  endproperty
  axi_errs_ruser_stable: assert property (AXI_ERRS_RUSER_STABLE) else
   $error("AXI_ERRS_RUSER_STABLE. RUSER must remain stable when RVALID is asserted and RREADY low. Spec: section 3.1, and figure 3-1, on page 3-2.");


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------
`ifdef AXI_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI_ERRM_AWUSER_X
  // =====
  property AXI_ERRM_AWUSER_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & AWVALID
        |-> ! $isunknown(AWUSER);
  endproperty
  axi_errm_awuser_x: assert property (AXI_ERRM_AWUSER_X) else
   $error("AXI_ERRM_AWUSER_X. When AWVALID is high, a value of X on AWUSER is not permitted. Spec: section 3.1.1 on page 3-3.");


  // INDEX:        - AXI_ERRM_WUSER_X
  // =====
  property AXI_ERRM_WUSER_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & WVALID
        |-> ! $isunknown(WUSER);
  endproperty
  axi_errm_wuser_x: assert property (AXI_ERRM_WUSER_X) else
   $error("AXI_ERRM_WUSER_X. When WVALID is high, a value of X on WUSER is not permitted.");


  // INDEX:        - AXI_ERRS_BUSER_X
  // =====
  property AXI_ERRS_BUSER_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & BVALID
        |-> ! $isunknown(BUSER);
  endproperty
  axi_errs_buser_x: assert property (AXI_ERRS_BUSER_X) else
   $error("AXI_ERRS_BUSER_X. When BVALID is high, a value of X on BUSER is not permitted.");


  // INDEX:        - AXI_ERRM_ARUSER_X
  // =====
  property AXI_ERRM_ARUSER_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & ARVALID
        |-> ! $isunknown(ARUSER);
  endproperty
  axi_errm_aruser_x: assert property (AXI_ERRM_ARUSER_X) else
   $error("AXI_ERRM_ARUSER_X. When ARVALID is high, a value of X on ARUSER is not permitted. Spec: section 3.1.4 on page 3-4.");


  // INDEX:        - AXI_ERRS_RUSER_X
  // =====
  property AXI_ERRS_RUSER_X;
    @(posedge `AXI_SVA_CLK)
        `AXI_SVA_RSTn & RVALID
        |-> ! $isunknown(RUSER);
  endproperty
  axi_errs_ruser_x: assert property (AXI_ERRS_RUSER_X) else
   $error("AXI_ERRS_RUSER_X. When RVALID is high, a value of X on RUSER is not permitted.");

`endif // AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:
// INDEX: Auxiliary Logic
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Rules for Auxiliary Logic
//------------------------------------------------------------------------------


  //----------------------------------------------------------------------------
  // INDEX:      a) Master (AUXM*)
  //----------------------------------------------------------------------------


  // INDEX:        - AXI_AUXM_DATA_WIDTH
  // =====
  property AXI_AUXM_DATA_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (DATA_WIDTH ==   32 ||
       DATA_WIDTH ==   64 ||
       DATA_WIDTH ==  128 ||
       DATA_WIDTH ==  256 ||
       DATA_WIDTH ==  512 ||
       DATA_WIDTH == 1024);
  endproperty
  axi_auxm_data_width: assert property (AXI_AUXM_DATA_WIDTH) else
   $error("AXI_AUXM_DATA_WIDTH. Parameter DATA_WIDTH must be 32, 64, 128, 256, 512 or 1024");


  // INDEX:        - AXI_AUXM_ADDR_WIDTH
  // =====
  property AXI_AUXM_ADDR_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (ADDR_WIDTH >= 32 && ADDR_WIDTH <= 64);
  endproperty
  axi_auxm_addr_width: assert property (AXI_AUXM_ADDR_WIDTH) else
   $error("AXI_AUXM_ADDR_WIDTH. Parameter ADDR_WIDTH must be between 32 and 64 bits inclusive");


  // INDEX:        - AXI_AUXM_AWUSER_WIDTH
  // =====
  property AXI_AUXM_AWUSER_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (AWUSER_WIDTH >= 1);
  endproperty
  axi_auxm_awuser_width: assert property (AXI_AUXM_AWUSER_WIDTH) else
   $error("AXI_AUXM_AWUSER_WIDTH. Parameter AWUSER_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_WUSER_WIDTH
  // =====
  property AXI_AUXM_WUSER_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (WUSER_WIDTH >= 1);
  endproperty
  axi_auxm_wuser_width: assert property (AXI_AUXM_WUSER_WIDTH) else
   $error("AXI_AUXM_WUSER_WIDTH. Parameter WUSER_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_BUSER_WIDTH
  // =====
  property AXI_AUXM_BUSER_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (BUSER_WIDTH >= 1);
  endproperty
  axi_auxm_buser_width: assert property (AXI_AUXM_BUSER_WIDTH) else
   $error("AXI_AUXM_BUSER_WIDTH. Parameter BUSER_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_ARUSER_WIDTH
  // =====
  property AXI_AUXM_ARUSER_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (ARUSER_WIDTH >= 1);
  endproperty
  axi_auxm_aruser_width: assert property (AXI_AUXM_ARUSER_WIDTH) else
   $error("AXI_AUXM_ARUSER_WIDTH. Parameter ARUSER_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_RUSER_WIDTH
  // =====
  property AXI_AUXM_RUSER_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (RUSER_WIDTH >= 1);
  endproperty
  axi_auxm_ruser_width: assert property (AXI_AUXM_RUSER_WIDTH) else
   $error("AXI_AUXM_RUSER_WIDTH. Parameter RUSER_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_ID_WIDTH
  // =====
  property AXI_AUXM_ID_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (ID_WIDTH >= 1);
  endproperty
  axi_auxm_id_width: assert property (AXI_AUXM_ID_WIDTH) else
   $error("AXI_AUXM_ID_WIDTH. Parameter ID_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_EXMON_WIDTH
  // =====
  property AXI_AUXM_EXMON_WIDTH;
    @(posedge `AXI_SVA_CLK)
      (EXMON_WIDTH >= 1);
  endproperty
  axi_auxm_exmon_width: assert property (AXI_AUXM_EXMON_WIDTH) else
   $error("AXI_AUXM_EXMON_WIDTH. Parameter EXMON_WIDTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_WDEPTH
  // =====
  property AXI_AUXM_WDEPTH;
    @(posedge `AXI_SVA_CLK)
      (WDEPTH >= 1);
  endproperty
  axi_auxm_wdepth: assert property (AXI_AUXM_WDEPTH) else
   $error("AXI_AUXM_WDEPTH. Parameter WDEPTH must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_MAXRBURSTS
  // =====
  property AXI_AUXM_MAXRBURSTS;
    @(posedge `AXI_SVA_CLK)
      (MAXRBURSTS >= 1);
  endproperty
  axi_auxm_maxrbursts: assert property (AXI_AUXM_MAXRBURSTS) else
   $error("AXI_AUXM_MAXRBURSTS. Parameter MAXRBURSTS must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_MAXWBURSTS
  // =====
  property AXI_AUXM_MAXWBURSTS;
    @(posedge `AXI_SVA_CLK)
      (MAXWBURSTS >= 1);
  endproperty
  axi_auxm_maxwbursts: assert property (AXI_AUXM_MAXWBURSTS) else
   $error("AXI_AUXM_MAXWBURSTS. Parameter MAXWBURSTS must be greater than or equal to 1");


  // INDEX:        - AXI_AUXM_RCAM_OVERFLOW
  // =====
  property AXI_AUXM_RCAM_OVERFLOW;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(RIndex))
      |-> (RIndex <= (MAXRBURSTS+1));
  endproperty
  axi_auxm_rcam_overflow: assert property (AXI_AUXM_RCAM_OVERFLOW) else
    $error("AXI_AUXM_RCAM_OVERFLOW. Read CAM overflow, increase MAXRBURSTS parameter.");


  // INDEX:        - AXI_AUXM_RCAM_UNDERFLOW
  // =====
  property AXI_AUXM_RCAM_UNDERFLOW;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(RIndex))
      |-> (RIndex > 0);
  endproperty
  axi_auxm_rcam_underflow: assert property (AXI_AUXM_RCAM_UNDERFLOW) else
   $error("AXI_AUXM_RCAM_UNDERFLOW. Read CAM underflow.");


  // INDEX:        - AXI_AUXM_WCAM_OVERFLOW
  // =====
  property AXI_AUXM_WCAM_OVERFLOW;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(WIndex))
      |-> (WIndex <= (MAXWBURSTS+1));
  endproperty
  axi_auxm_wcam_overflow: assert property (AXI_AUXM_WCAM_OVERFLOW) else
   $error("AXI_AUXM_WCAM_OVERFLOW. Write CAM overflow, increase MAXWBURSTS parameter.");


  // INDEX:        - AXI_AUXM_WCAM_UNDERFLOW
  // =====
  property AXI_AUXM_WCAM_UNDERFLOW;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(WIndex))
      |-> (WIndex > 0);
  endproperty
  axi_auxm_wcam_underflow: assert property (AXI_AUXM_WCAM_UNDERFLOW) else
   $error("AXI_AUXM_WCAM_UNDERFLOW. Write CAM underflow");


  // INDEX:        - AXI_AUXM_EXCL_OVERFLOW
  // =====
  property AXI_AUXM_EXCL_OVERFLOW;
    @(posedge `AXI_SVA_CLK)
      `AXI_SVA_RSTn & !($isunknown(ExclIdOverflow))
      |-> (!ExclIdOverflow);
  endproperty
  axi_auxm_excl_overflow: assert property (AXI_AUXM_EXCL_OVERFLOW) else
   $error("AXI_AUXM_EXCL_OVERFLOW. Exclusive access monitor overflow, increase EXMON_WIDTH parameter.");


//------------------------------------------------------------------------------
// INDEX:   2) Combinatorial Logic
//------------------------------------------------------------------------------


  //----------------------------------------------------------------------------
  // INDEX:      a) Masks
  //----------------------------------------------------------------------------


  // INDEX:           - AlignMaskR
  // =====
  // Calculate wrap mask for read address
  always @(ARSIZE or ARVALID)
  begin
    if (ARVALID)
      case (ARSIZE)
        `AXI_ASIZE_1024:  AlignMaskR = 7'b0000000;
        `AXI_ASIZE_512:   AlignMaskR = 7'b1000000;
        `AXI_ASIZE_256:   AlignMaskR = 7'b1100000;
        `AXI_ASIZE_128:   AlignMaskR = 7'b1110000;
        `AXI_ASIZE_64:    AlignMaskR = 7'b1111000;
        `AXI_ASIZE_32:    AlignMaskR = 7'b1111100;
        `AXI_ASIZE_16:    AlignMaskR = 7'b1111110;
        `AXI_ASIZE_8:     AlignMaskR = 7'b1111111;
        default:          AlignMaskR = 7'b1111111;
      endcase
    else
      AlignMaskR = 7'b1111111;
  end


  // INDEX:           - AlignMaskW
  // =====
  // Calculate wrap mask for write address
  always @(AWSIZE or AWVALID)
  begin
    if (AWVALID)
      case (AWSIZE)
        `AXI_ASIZE_1024:  AlignMaskW = 7'b0000000;
        `AXI_ASIZE_512:   AlignMaskW = 7'b1000000;
        `AXI_ASIZE_256:   AlignMaskW = 7'b1100000;
        `AXI_ASIZE_128:   AlignMaskW = 7'b1110000;
        `AXI_ASIZE_64:    AlignMaskW = 7'b1111000;
        `AXI_ASIZE_32:    AlignMaskW = 7'b1111100;
        `AXI_ASIZE_16:    AlignMaskW = 7'b1111110;
        `AXI_ASIZE_8:     AlignMaskW = 7'b1111111;
        default:          AlignMaskW = 7'b1111111;
      endcase // case(AWSIZE)
    else
      AlignMaskW = 7'b1111111;
  end


  // INDEX:           - ExclMask
  // =====
  always @(ARLEN or ARSIZE)
  begin : p_ExclMaskComb
    ExclMask = ~((({7'b000_0000, ARLEN} + 11'b000_0000_0001) << ARSIZE) - 11'b000_0000_0001);
  end // block: p_ExclMaskComb


  // INDEX:           - WdataMask
  // =====
  always @(WSTRB)
  begin : p_WdataMaskComb
    integer i;  // data byte loop counter
    integer j;  // data bit loop counter

    for (i = 0; i < STRB_WIDTH; i = i + 1)
      for (j = i * 8; j <= (i * 8) + 7; j = j + 1)
        WdataMask[j] = WSTRB[i];
  end


  // INDEX:           - RdataMask
  // =====
  assign RdataMask = ReadDataMask(RBurstCam[RidMatch], RCountCam[RidMatch]);


  //----------------------------------------------------------------------------
  // INDEX:      b) Increments
  //----------------------------------------------------------------------------


  // INDEX:           - ArAddrIncr
  // =====
  always @(ARSIZE or ARLEN or ARADDR)
  begin : p_RAddrIncrComb
    ArAddrIncr = ARADDR + (ARLEN << ARSIZE);  // The final address of the burst
  end


  // INDEX:           - AwAddrIncr
  // =====
  always @(AWSIZE or AWLEN or AWADDR)
  begin : p_WAddrIncrComb
    AwAddrIncr = AWADDR + (AWLEN << AWSIZE);  // The final address of the burst
  end


  //----------------------------------------------------------------------------
  // INDEX:      c) Conversions
  //----------------------------------------------------------------------------


  // INDEX:           - ArLenInBytes
  // =====
  always @(ARSIZE or ARLEN)
  begin : p_ArLenInBytes
    ArLenInBytes = (({8'h00, ARLEN} + 12'h001) << ARSIZE); // bytes = (ARLEN+1) data transfers x ARSIZE bytes
  end


  // INDEX:           - ArSizeInBits
  // =====
  always @(ARSIZE)
  begin : p_ArSizeInBits
    ArSizeInBits = (11'b000_0000_1000 << ARSIZE); // bits = 8 x ARSIZE bytes
  end


  // INDEX:           - AwSizeInBits
  // =====
  always @(AWSIZE)
  begin : p_AwSizeInBits
    AwSizeInBits = (11'b000_0000_1000 << AWSIZE); // bits = 8 x AWSIZE bytes
  end


  //----------------------------------------------------------------------------
  // INDEX:      d) Other
  //----------------------------------------------------------------------------


  // INDEX:           - ArExclPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArExclPending = RBurstCam[RidMatch][EXCL];


  // INDEX:           - ArLenPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArLenPending = {1'b0, RBurstCam[RidMatch][ALENHI:ALENLO]};

  // INDEX:           - ArCountPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArCountPending = RCountCam[RidMatch];


//------------------------------------------------------------------------------
// INDEX:   3) EXCL & LOCK Accesses
//------------------------------------------------------------------------------


  // INDEX:        - Exclusive Access ID Lookup
  // =====
  // Map transaction IDs to the available exclusive access storage loactions

  // Lookup table for IDs used by the exclusive access monitor
  // Each location in the table has a valid flag to indicate if the ID is in use
  // The location of an ID flagged as valid is used as a virtual ID in the
  // exclusive access monitor checks
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_ExclIdSeq
    integer i;  // loop counter
    if (!`AXI_AUX_RSTn)
    begin
      ExclIdValid <= {EXMON_HI+1{1'b0}};
      ExclIdDelta <= 1'b0;
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        ExclId[i] <= {ID_WIDTH{1'b0}};
      end
    end
    else // clk edge
    begin
      // exclusive read address transfer
      if (ARVALID && ARREADY && (ARLOCK == `AXI_ALOCK_EXCL) &&
          !ExclIdFull)
      begin
        ExclId[ExclIdWrPtr] <= ARID;
        ExclIdValid[ExclIdWrPtr] <= 1'b1;
        ExclIdDelta <= ~ExclIdDelta;
      end
      // exclusive write
      if (AWVALID && AWREADY && (AWLOCK == `AXI_ALOCK_EXCL) &&
          ExclAwMatch)
      begin
        ExclIdValid[ExclAwId] <= 1'b0;
        ExclIdDelta <= ~ExclIdDelta;
      end
    end // else: !if(!`AXI_AUX_RSTn)
  end // block: p_ExclIdSeq

  // Lookup table is full when all valid bits are set
  assign ExclIdFull = &ExclIdValid;

  // Lookup table overflows when it is full and another exclusive read happens
  // with an ID that does not match any already being monitored
  assign ExclIdOverflow = ExclIdFull &&
                          ARVALID && ARREADY && (ARLOCK == `AXI_ALOCK_EXCL) &&
                          !ExclRMatch;

  // New IDs are written to the highest location
  // that does not have the valid flag set 
  always @(ExclIdValid or ExclIdDelta)
  begin : p_ExclIdFreePtrComb
    integer i;  // loop counter
    ExclIdFreePtr = 0;
    for (i = 0; i <= EXMON_HI; i = i + 1)
    begin
      if (ExclIdValid[i] == 1'b0)
      begin
        ExclIdFreePtr = i;
      end
    end
  end // p_ExclIdFreePtrComb

  // If the ID is already being monitored then reuse the location
  // New IDs are written to the highest location
  // that does not have the valid flag set 
  assign ExclIdWrPtr = ExclArMatch ? ExclArId : ExclIdFreePtr;

  // Write address ID comparator
  always @(AWVALID or AWID or ExclIdValid or ExclIdDelta)
  begin : p_ExclAwMatchComb
    integer i;  // loop counter
    ExclAwMatch = 1'b0;
    ExclAwId = {EXMON_WIDTH{1'b0}};
    if (AWVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (AWID == ExclId[i]))
        begin
          ExclAwMatch = 1'b1;
          ExclAwId = i;
        end
      end
    end
  end // p_ExclAwMatchComb

  // Read address ID comparator
  always @(ARVALID or ARID or ExclIdValid or ExclIdDelta)
  begin : p_ExclArMatchComb
    integer i;  // loop counter
    ExclArMatch = 1'b0;
    ExclArId = {EXMON_WIDTH{1'b0}};
    if (ARVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (ARID == ExclId[i]))
        begin
          ExclArMatch = 1'b1;
          ExclArId = i;
        end
      end
    end
  end // p_ExclArMatchComb

  // Read data ID comparator
  always @(RVALID or RID or ExclIdValid or ExclIdDelta)
  begin : p_ExclRMatchComb
    integer i;  // loop counter
    ExclRMatch = 1'b0;
    ExclRId = {EXMON_WIDTH{1'b0}};
    if (RVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (RID == ExclId[i]))
        begin
          ExclRMatch = 1'b1;
          ExclRId = i;
        end
      end
    end
  end // p_ExclRMatchComb

  // INDEX:        - Exclusive Access Storage
  // =====
  // Store exclusive control info on each read for checking against write

  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_ExclCtrlSeq
    integer i;  // loop counter

    if (!`AXI_AUX_RSTn)
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        ExclReadAddr[i] <= 1'b0;
        ExclReadData[i] <= 1'b0;
        ExclAddr[i]     <= {ADDR_WIDTH{1'b0}};
        ExclSize[i]     <= 3'b000;
        ExclLen[i]      <= 4'h0;
        ExclBurst[i]    <= 2'b00;
        ExclCache[i]    <= 4'h0;
        ExclProt[i]     <= 3'b000;
        ExclUser[i]     <= {ARUSER_WIDTH{1'b0}};
      end
    else // clk edge
    begin
      // exclusive read address transfer
      if (ARVALID && ARREADY && (ARLOCK == `AXI_ALOCK_EXCL) &&
          !ExclIdFull)
      begin
        ExclReadAddr[ExclIdWrPtr] <= 1'b1; // set exclusive read addr flag for ARID
        ExclReadData[ExclIdWrPtr] <= 1'b0; // reset exclusive read data flag for ARID
        ExclAddr[ExclIdWrPtr]     <= ARADDR;
        ExclSize[ExclIdWrPtr]     <= ARSIZE;
        ExclLen[ExclIdWrPtr]      <= ARLEN;
        ExclBurst[ExclIdWrPtr]    <= ARBURST;
        ExclCache[ExclIdWrPtr]    <= ARCACHE;
        ExclProt[ExclIdWrPtr]     <= ARPROT;
        ExclUser[ExclIdWrPtr]     <= ARUSER;
      end
      // exclusive write
      if (AWVALID && AWREADY && (AWLOCK == `AXI_ALOCK_EXCL) &&
          ExclAwMatch)
      begin
        ExclReadAddr[ExclAwId] <= 1'b0; // reset exclusive address flag for AWID
        ExclReadData[ExclAwId] <= 1'b0; // reset exclusive read data flag for AWID
      end
      // completion of exclusive read data transaction
      if ((RVALID && RREADY && RLAST && ExclReadAddr[ExclRId] &&
           ExclRMatch) &&
           // check the read CAM that this is part of an exclusive transfer
           RBurstCam[RidMatch][EXCL]
         )
        ExclReadData[ExclRId]  <= 1'b1; // set exclusive read data flag for RID
    end // else: !if(!`AXI_AUX_RSTn)
  end // block: p_ExclCtrlSeq


  // INDEX:        - Lock State Machine
  // =====
  // The state machine transitions when address valid
  always @( ARLOCK or ARNew or
            AWLOCK or AWNew or
            LockState)
  begin : p_LockStateNextComb
    case (LockState)
      `AXI_AUX_ST_UNLOCKED :
        if ((ARNew & (ARLOCK == `AXI_ALOCK_LOCKED)) ||
            (AWNew & (AWLOCK == `AXI_ALOCK_LOCKED)))
          LockStateNext = `AXI_AUX_ST_LOCKED;
        else
          LockStateNext = `AXI_AUX_ST_UNLOCKED;

      `AXI_AUX_ST_LOCKED :
        if ((ARNew & (ARLOCK != `AXI_ALOCK_LOCKED)) ||
            (AWNew & (AWLOCK != `AXI_ALOCK_LOCKED)))
          LockStateNext = `AXI_AUX_ST_LOCK_LAST;
        else
          LockStateNext = `AXI_AUX_ST_LOCKED;

      `AXI_AUX_ST_LOCK_LAST :
        if ((ARNew & (ARLOCK == `AXI_ALOCK_LOCKED)) ||
            (AWNew & (AWLOCK == `AXI_ALOCK_LOCKED)))
          LockStateNext = `AXI_AUX_ST_LOCKED;

        else if ((ARNew & (ARLOCK != `AXI_ALOCK_LOCKED)) ||
                 (AWNew & (AWLOCK != `AXI_ALOCK_LOCKED)))
          LockStateNext = `AXI_AUX_ST_UNLOCKED;
        else
          LockStateNext = `AXI_AUX_ST_LOCK_LAST;

      `AXI_AUX_ST_NOT_USED : LockStateNext = 2'bXX;
                // Unreachable encoding, so X assigned for synthesis don't-care

      default            : LockStateNext = 2'bXX; // X-propagation
    endcase // case(LockState)
  end // always p_LockStateNextComb


  // INDEX:        - Lock State Register
  // =====
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_LockStateSeq
    if (!`AXI_AUX_RSTn)
    begin
      LockState <= `AXI_AUX_ST_UNLOCKED;
      LockId    <= {ID_WIDTH{1'b0}};
      LockCache <= 4'b0000;
      LockProt  <= 3'b000;
      LockAddr  <= {ADDR_WIDTH{1'b0}};
    end
    else
    begin
      LockState <= LockStateNext;
      LockId    <= LockIdNext;
      LockCache <= LockCacheNext;
      LockProt  <= LockProtNext;
      LockAddr  <= LockAddrNext;
    end
  end


  // INDEX:        - Lock Property Logic
  // =====

  // registering write/read ready/valid values
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_ValidReadyReg
    if (!`AXI_AUX_RSTn)
    begin
      PrevAWVALID <= 1'b0;
      PrevAWREADY <= 1'b0;
      PrevARVALID <= 1'b0;
      PrevARREADY <= 1'b0;
    end
    else
    begin
      PrevAWVALID <= AWVALID;
      PrevAWREADY <= AWREADY;
      PrevARVALID <= ARVALID;
      PrevARREADY <= ARREADY;
    end
  end

  // AWNew=1 for the first cycle valid of a write address
  assign AWNew = (AWVALID & ~PrevAWVALID) |
                 (AWVALID & PrevAWVALID & PrevAWREADY);

  // ARNew=1 for the first cycle valid of a read address
  assign ARNew = (ARVALID & ~PrevARVALID) |
                 (ARVALID & PrevARVALID & PrevARREADY);

  // AWLockNew=1 for the first cycle of the initial locking write address
  // valid for a locked sequence
  assign AWLockNew  = (
                        (LockState == `AXI_AUX_ST_UNLOCKED) ||
                        (LockState == `AXI_AUX_ST_LOCK_LAST)
                      ) & AWNew & (AWLOCK == `AXI_ALOCK_LOCKED);

  // ARLockNew=1 for the first cycle of the initial locking read address
  // valid for a locked sequence
  assign ARLockNew  = (
                        (LockState == `AXI_AUX_ST_UNLOCKED) ||
                        (LockState == `AXI_AUX_ST_LOCK_LAST)
                      ) & ARNew & (ARLOCK == `AXI_ALOCK_LOCKED);

  // AWLockLastNew=1 for the first cycle of the unlocking write address
  // valid for a locked sequence
  assign AWLockLastNew  = (LockState == `AXI_AUX_ST_LOCKED) &
                          AWNew & (AWLOCK != `AXI_ALOCK_LOCKED);

  // ARLockLastNew=1 for the first cycle of the unlocking read address
  // valid for a locked sequence
  assign ARLockLastNew  = (LockState == `AXI_AUX_ST_LOCKED) &
                          ARNew & (ARLOCK != `AXI_ALOCK_LOCKED);


  // Store the ID of the first locked transfer
  always @(AWLockNew or ARLockNew or
            LockId or AWID or ARID)
  begin : p_LockIdNextComb
    case ({ARLockNew,AWLockNew})
      2'b00 : LockIdNext = LockId;      // No new locked burst
      2'b01 : LockIdNext = AWID;        // New locked write burst
      2'b10 : LockIdNext = ARID;        // New locked read burst
      2'b11 : LockIdNext = AWID;        // Both new locked write and read bursts
      default : LockIdNext = {ID_WIDTH{1'bx}};  // X propagation
    endcase
  end // p_LockIdNextComb

  // Store the AxCACHE of the first locked transfer
  always @(AWLockNew or ARLockNew or
            LockCache or AWCACHE or ARCACHE)
  begin : p_LockCacheNextComb
    case ({ARLockNew,AWLockNew})
      2'b00 : LockCacheNext = LockCache;// No new locked burst
      2'b01 : LockCacheNext = AWCACHE;  // New locked write burst
      2'b10 : LockCacheNext = ARCACHE;  // New locked read burst
      2'b11 : LockCacheNext = AWCACHE;  // Both new locked write and read bursts
      default : LockCacheNext = 4'bxxxx;  // X propagation
    endcase
  end // p_LockCacheNextComb


  // Store the AxPROT of the first locked transfer
  always @(AWLockNew or ARLockNew or
            LockProt or AWPROT or ARPROT)
  begin : p_LockProtNextComb
    case ({ARLockNew,AWLockNew})
      2'b00 : LockProtNext = LockProt;  // No new locked burst
      2'b01 : LockProtNext = AWPROT;    // New locked write burst
      2'b10 : LockProtNext = ARPROT;    // New locked read burst
      2'b11 : LockProtNext = AWPROT;    // Both new locked write and read bursts
      default : LockProtNext = 3'bxxx;    // X propagation
    endcase
  end // p_LockProtNextComb

  // Store the AxADDR of the first locked transfer
  always @(AWLockNew or ARLockNew or
            LockAddr or AWADDR or ARADDR)
  begin : p_LockAddrNextComb
    case ({ARLockNew,AWLockNew})
      2'b00 : LockAddrNext = LockAddr;  // No new locked burst
      2'b01 : LockAddrNext = AWADDR;    // New locked write burst
      2'b10 : LockAddrNext = ARADDR;    // New locked read burst
      2'b11 : LockAddrNext = AWADDR;    // Both new locked write and read bursts
      default : LockAddrNext = {ADDR_WIDTH{1'bX}};  // X propagation
    endcase
  end // p_LockAddrNextComb


//------------------------------------------------------------------------------
// INDEX:   4) Content addressable memories (CAMs)
//------------------------------------------------------------------------------


  // INDEX:        - Read CAMSs (CAM+Shift)
  // =====
  // New entries are added at the end of the CAM.
  // Elements may be removed from any location in the CAM, determined by the
  // first matching RID. When an element is removed, remaining elements
  // with a higher index are shifted down to fill the empty space.

  // Read CAMs store all outstanding addresses for read transactions
  assign RPush  = ARVALID & ARREADY;        // Push on address handshake
  assign RPop   = RVALID & RREADY & RLAST;  // Pop on last handshake

  // Flag when there are no outstanding read transactions
  assign nROutstanding = (RIndex == 1);

  // Find the index of the first item in the CAM that matches the current RID
  // (Note that RIdCamDelta is used to determine when RIdCam has changed)
  always @(RID or RIndex or RIdCamDelta)
  begin : p_RidMatch
    integer i;  // loop counter
    RidMatch = 0;
    for (i=MAXRBURSTS; i>0; i=i-1)
      if ((i < RIndex) && (RID == RBurstCam[i][IDHI:IDLO]))
        RidMatch = i;
  end

  // Update the flags indicating if RBurstCam contains locked/unlocked
  // transactions
  // (Note that RIdCamDelta is used to determine when RIdCam has changed)
  always @(RIndex or RIdCamDelta)
  begin : p_TxxRcamUpdate
    integer i; // loop counter
    UnlockedInRCam = 1'b0;
    LockedInRCam = 1'b0;
    for (i=MAXRBURSTS; i>0; i=i-1)
    begin
      if (i < RIndex)
      begin
        if (RBurstCam[i][LOCKED])
          LockedInRCam = 1'b1;
        else
          UnlockedInRCam = 1'b1;
      end
    end
  end

  // Combine cam flags with current bus state to drive the flags
  // indicating which types of lock read transactions are present
  // on the bus (if any)
  assign LockedRead   = LockedInRCam ||
                        (ARVALID && (ARLOCK == `AXI_ALOCK_LOCKED));
  assign UnlockedRead = UnlockedInRCam ||
                        (ARVALID && (ARLOCK != `AXI_ALOCK_LOCKED));

  // Calculate the index of the next free element in the CAM
  always @(RIndex or RPop or RPush)
  begin : p_RIndexNextComb
    case ({RPush,RPop})
      2'b00   : RIndexNext = RIndex;      // no push, no pop
      2'b01   : RIndexNext = RIndex - 1;  // pop, no push
      2'b10   : RIndexNext = RIndex + 1;  // push, no pop
      2'b11   : RIndexNext = RIndex;      // push and pop
      default : RIndexNext = 'bX;         // X-propagation
    endcase
  end
  //
  // RIndex Register
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_RIndexSeq
    if (!`AXI_AUX_RSTn)
      RIndex <= 1;
    else
      RIndex <= RIndexNext;
  end
  //
  // CAM Implementation
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_ReadCam
    reg [RBURSTMAX:0] Burst; // temporary store for burst data structure
    if (!`AXI_AUX_RSTn)
    begin : p_ReadCamReset
      integer i;  // loop counter
      // Reset all the entries in the CAM
      for (i=1; i<=MAXRBURSTS; i=i+1)
      begin
        RBurstCam[i] <= {RBURSTMAX+1{1'b0}};
        RCountCam[i] <= 5'h0;
        RIdCamDelta  <= 1'b0;
      end
    end
    else

    begin

      // Pop item from the CAM, at location determined by RidMatch
      if (RPop)
      begin : p_ReadCamPop
        integer i;  // loop counter
        // Delete item by shifting remaining items
        for (i=1; i<MAXRBURSTS; i=i+1)
          if (i >= RidMatch)
          begin
            RBurstCam[i] <= RBurstCam[i+1];
            RCountCam[i] <= RCountCam[i+1];
            RIdCamDelta <= ~RIdCamDelta;
          end
      end
      else
        // if not last data item, increment beat count
        if (RVALID & RREADY)
          RCountCam[RidMatch] <= RCountCam[RidMatch] + 5'h01;

      Burst[ADDRHI:ADDRLO]   = ARADDR[ADDRHI:ADDRLO];
      Burst[EXCL]            = (ARLOCK == `AXI_ALOCK_EXCL);
      Burst[LOCKED]          = (ARLOCK == `AXI_ALOCK_LOCKED);
      Burst[BURSTHI:BURSTLO] = ARBURST;
      Burst[ALENHI:ALENLO]   = ARLEN;
      Burst[ASIZEHI:ASIZELO] = ARSIZE;
      Burst[IDHI:IDLO]       = ARID;

      // Push item at end of the CAM
      // Note that the value of the final index in the CAM is depends on
      // whether another item has been popped
      if (RPush)
      begin
        if (RPop)
        begin
          RBurstCam[RIndex-1] <= Burst;
          RCountCam[RIndex-1] <= 5'h00;
        end
        else
        begin
          RBurstCam[RIndex]   <= Burst;
          RCountCam[RIndex]   <= 5'h00;
        end // else: !if(RPop)
        RIdCamDelta <= ~RIdCamDelta;
      end // if (RPush)
    end // else: if(!`AXI_AUX_RSTn)
  end // always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)


  // INDEX:        - Write CAMs (CAM+Shift)
  // =====
  // New entries are added at the end of the CAM.
  // Elements may be removed from any location in the CAM, determined by the
  // first matching WID and/or BID. When an element is removed, remaining
  // elements with a higher index are shifted down to fill the empty space.


  // Write bursts stored in single structure for checking when complete.
  // This avoids the problem of early write data.
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_WriteCam
    reg [WBURSTMAX:0] Burst; // temporary store for burst data structure
    integer i;               // loop counter
    if (!`AXI_AUX_RSTn)
    begin : p_WriteCamReset
      for (i=1; i<=MAXWBURSTS; i=i+1)
      begin
        WBurstCam[i]  = {WBURSTMAX+1{1'b0}}; // initialise to zero on reset
        WCountCam[i]  = 5'b0; // initialise beat counters to zero
        WLastCam[i]   = 1'b0;
        WAddrCam[i]   = 1'b0;
        BRespCam[i]   = 1'b0;
      end
      WIndex   = 1;
      AidMatch = 1;
      BidMatch = 1;
      WidMatch = 1;
      Burst    = {WBURSTMAX+1{1'b0}};
      AWDataNumError  <= 1'b0;
      WDataNumError   <= 1'b0;
      WDataOrderError <= 1'b0;
      BrespError      <= 1'b0;
      BrespExokError  <= 1'b0;
      AWStrbError     <= 1'b0;
      BStrbError      <= 1'b0;
      BrespLeadingRec <= 1'b0;
      nWAddrTrans     <= 1'b1;
      UnlockedInWCam  <= 1'b0;
      LockedInWCam    <= 1'b0;
      FlagUNInWCam    <= 1'b0;
      FlagLOInWCam    <= 1'b0;
      FlagLLInWCam    <= 1'b0;
   end
    else
    begin
      // default is no errors
      AWDataNumError  <= 1'b0;
      WDataNumError   <= 1'b0;
      WDataOrderError <= 1'b0;
      BrespError      <= 1'b0;
      BrespExokError  <= 1'b0;
      AWStrbError     <= 1'b0;
      BStrbError      <= 1'b0;
      BrespLeadingRec <= 1'b0;

      // -----------------------------------------------------------------------
      // Valid write response
      if (BVALID)
      begin

        // Find matching burst
        begin : p_WriteCamMatchB

          BidMatch = WIndex; // default is no match
          for (i=MAXWBURSTS; i>0; i=i-1)
            if (i < WIndex) // only consider valid entries in WBurstCam
            begin
              Burst = WBurstCam[i];
              if (BID == Burst[IDHI:IDLO] && // BID matches, and
                  ~BRespCam[i]) // write response not already transferred
                BidMatch = i;
            end
        end // p_WriteCamMatchB

        Burst = WBurstCam[BidMatch];  // set temporary burst signal

        BRespCam[BidMatch] = BREADY;  // record if write response completed


        // Check that BID matches outstanding WID or AWID
        if (~(BidMatch < WIndex))
          BrespError <= 1'b1;         // trigger AXI_ERRS_BRESP

        // The following checks are only performed if the write response matches
        // an existing burst
        else begin

          // Check all write data in burst is complete
          // Note: this test must occur before the WLastCam is updated
          if (~WLastCam[BidMatch]) // last data not received
            BrespError <= 1'b1;         // trigger AXI_ERRS_BRESP

          // Check for EXOKAY response to non-exclusive transaction
          if (Burst[EXCL] == 1'b0 && BRESP == `AXI_RESP_EXOKAY)
            BrespExokError <= 1'b1;

          // Check if a write address has not been received and
          // flag that this not recommended
          // This must be done before the CAMs are popped when the
          // the address has been received
          if (!WAddrCam[BidMatch])
            BrespLeadingRec <= 1'b1;

          // Write response handshake completes burst when write address has
          // already been received, and triggers protocol checking
          if (BREADY & WAddrCam[BidMatch])
          begin : p_WriteCamPopB
            // Check WSTRB
            BStrbError <= CheckBurst(WBurstCam[BidMatch], WCountCam[BidMatch]);

            // pop completed burst from CAM
            for (i = 1; i < MAXWBURSTS; i = i+1)
            begin
              if (i >= BidMatch) // only shift items after popped burst
              begin
                WBurstCam[i]   = WBurstCam[i+1];
                WCountCam[i]   = WCountCam[i+1];
                WLastCam[i]    = WLastCam[i+1];
                WAddrCam[i]    = WAddrCam[i+1];
                BRespCam[i]    = BRespCam[i+1];
              end
            end

            WIndex = WIndex - 1; // decrement index

            // Reset flags on new empty element
            WBurstCam[WIndex]  = {WBURSTMAX+1{1'b0}};
            WCountCam[WIndex]  = 5'b0;
            WLastCam[WIndex]   = 1'b0;
            WAddrCam[WIndex]   = 1'b0;
            BRespCam[WIndex]   = 1'b0;

          end // if (BREADY & WAddrCam[BidMatch])

        end // else !(~(BidMatch < WIndex))
      end // if (BVALID)

      // -----------------------------------------------------------------------
      // Valid write data
      if (WVALID)
      begin : p_WriteCamWValid

        // find matching burst in progress
        WidMatch = WIndex; // default - no match
        for (i = MAXWBURSTS; i > 0; i = i-1)
          if (i < WIndex) // only consider valid entries in WBurstCam
          begin
            Burst = WBurstCam[i];
            if (WID == Burst[IDHI:IDLO] &&  // ID matches
                ~WLastCam[i])             // not already received last data item
              WidMatch = i;
          end

        Burst = WBurstCam[WidMatch]; // temp store for 2-D burst lookup

        // if last data item or correct number of data items received already,
        // check number of data items and WLAST against AWLEN.
        // WCountCam hasn't yet incremented so can be compared with AWLEN
        if  ( WAddrCam[WidMatch] & // Only perform test if address is known
              ( (WLAST & (WCountCam[WidMatch] != {1'b0,Burst[ALENHI:ALENLO]})) |
                (~WLAST & (WCountCam[WidMatch] == {1'b0,Burst[ALENHI:ALENLO]}))
              )
            )
          WDataNumError <= 1'b1;

        // if 1st data item, check that earlier bursts have all got 1st data
        // item to enforce the AXI_ERRM_WDATA_ORDER protocol rule
        if (WCountCam[WidMatch] == 5'b0)
        begin
          for (i = 1; i <= MAXWBURSTS; i = i+1)
            if (i < WidMatch)
              if (WCountCam[i] == 0)
                WDataOrderError <= 1'b1;
        end

        // need to use full case statement to occupy WSTRB as in Verilog the
        // bit slice range must be bounded by constant expressions
        case (WCountCam[WidMatch])
          5'h0 : Burst[STRB1HI:STRB1LO]   = WSTRB;
          5'h1 : Burst[STRB2HI:STRB2LO]   = WSTRB;
          5'h2 : Burst[STRB3HI:STRB3LO]   = WSTRB;
          5'h3 : Burst[STRB4HI:STRB4LO]   = WSTRB;
          5'h4 : Burst[STRB5HI:STRB5LO]   = WSTRB;
          5'h5 : Burst[STRB6HI:STRB6LO]   = WSTRB;
          5'h6 : Burst[STRB7HI:STRB7LO]   = WSTRB;
          5'h7 : Burst[STRB8HI:STRB8LO]   = WSTRB;
          5'h8 : Burst[STRB9HI:STRB9LO]   = WSTRB;
          5'h9 : Burst[STRB10HI:STRB10LO] = WSTRB;
          5'hA : Burst[STRB11HI:STRB11LO] = WSTRB;
          5'hB : Burst[STRB12HI:STRB12LO] = WSTRB;
          5'hC : Burst[STRB13HI:STRB13LO] = WSTRB;
          5'hD : Burst[STRB14HI:STRB14LO] = WSTRB;
          5'hE : Burst[STRB15HI:STRB15LO] = WSTRB;
          5'hF : Burst[STRB16HI:STRB16LO] = WSTRB;
          default : Burst[STRB16HI:STRB16LO] = {STRB_WIDTH{1'bx}};
        endcase

        // Store the WID in the CAM
        Burst[IDHI:IDLO] = WID; // record ID in case address not yet received
        WBurstCam[WidMatch] = Burst; // copy back from temp store

        // when write data transfer completes, determine if last
        WLastCam[WidMatch] = WLAST & WREADY; // record whether last data completed

        // When transfer completes, increment the count
        WCountCam[WidMatch] =
          WREADY ? WCountCam[WidMatch] + 5'b00001:    // inc count
                   WCountCam[WidMatch];


        if (WidMatch == WIndex) // if new burst, increment CAM index
          WIndex = WIndex + 1;

      end // if (WVALID)

      // -----------------------------------------------------------------------
      // Valid write address
      if (AWVALID)
      begin

        // find matching burst in progress
        begin : p_WriteCamMatchAw

          AidMatch = WIndex; // assume no match

          for (i = MAXWBURSTS; i > 0; i = i-1)
            if (i < WIndex) // only consider valid entries in WBurstCam
            begin
              Burst = WBurstCam[i];
              if (AWID == Burst[IDHI:IDLO] &&  // AWID matches, and
                  ~WAddrCam[i]) // write address not already transferred
                AidMatch = i;
            end
        end // p_WriteCamMatchAw

        Burst = WBurstCam[AidMatch];

        Burst[ADDRHI:ADDRLO]   = AWADDR[ADDRHI:ADDRLO];
        Burst[EXCL]            = AWLOCK[0];
        Burst[LOCKED]          = (AWLOCK == `AXI_ALOCK_LOCKED);
        Burst[BURSTHI:BURSTLO] = AWBURST;
        Burst[ALENHI:ALENLO]   = AWLEN;
        Burst[ASIZEHI:ASIZELO] = AWSIZE;
        Burst[IDHI:IDLO]       = AWID;

        WBurstCam[AidMatch] = Burst;  // copy back from temp store

        WAddrCam[AidMatch] = AWREADY; // record if write address completed

        // assert protocol error flag if address received after leading write
        // data and:
        // - WLAST was asserted when the beat count is less than AWLEN
        // - WLAST was not asserted when the beat count is equal to AWLEN
        // - the beat count is greater than AWLEN
        if ((WLastCam[AidMatch] &
              (({1'b0, Burst[ALENHI:ALENLO]} + 5'b00001) > WCountCam[AidMatch])) ||
            (~WLastCam[AidMatch] &
              (({1'b0, Burst[ALENHI:ALENLO]} + 5'b00001) == WCountCam[AidMatch])) ||
            (({1'b0, Burst[ALENHI:ALENLO]} + 5'b00001) < WCountCam[AidMatch]))
          AWDataNumError <= 1'b1;

        // Check that earlier bursts have all got address to enforce the
        // AXI_ERRM_WDATA_ORDER protocol rule
        begin : p_WriteCamWdataOrder

          for (i = 1; i <= MAXWBURSTS; i=i+1)
            begin
              if (i < AidMatch)             // check all earlier bursts
                if (WAddrCam[i] != 1'b1)    // address not yet received
                  WDataOrderError <= 1'b1;  // trigger assertion
            end
        end // p_WriteCamWdataOrder

        // If new burst, increment CAM index
        if (AidMatch == WIndex)
          WIndex = WIndex + 1;

        // Write address handshake completes burst when write response has
        // already been received, and triggers protocol checking
        else if (AWREADY & BRespCam[AidMatch])
        begin : p_WriteCamPopAw
          // Check WSTRB
          AWStrbError <= CheckBurst(WBurstCam[AidMatch], WCountCam[AidMatch]);

          // pop completed burst from CAM
          for (i = 1; i < MAXWBURSTS; i = i+1)
            if (i >= AidMatch) // only shift items after popped burst
            begin
              WBurstCam[i]    = WBurstCam[i+1];
              WCountCam[i]    = WCountCam[i+1];
              WLastCam[i]     = WLastCam[i+1];
              WAddrCam[i]     = WAddrCam[i+1];
              BRespCam[i]     = BRespCam[i+1];
            end

          WIndex = WIndex - 1; // decrement index

          // Reset flags on new empty element
          WBurstCam[WIndex]  = {WBURSTMAX+1{1'b0}};
          WCountCam[WIndex]  = 5'b0;
          WLastCam[WIndex]   = 1'b0;
          WAddrCam[WIndex]   = 1'b0;
          BRespCam[WIndex]   = 1'b0;

        end // if (AWREADY & BRespCam[AidMatch])

      end // new write address

      // Update all write transactions with the coincident transaction info
      // given by the locked/unlocked flags and the lock state of the
      // current cycle
      for (i = 1; i <= MAXWBURSTS; i = i+1)
      begin
        if (i < WIndex) // only consider valid entries in WBurstCam
        begin
          case (LockStateNext)
            `AXI_AUX_ST_UNLOCKED :
            begin
              if (UnlockedRead | UnlockedWrite)
                WBurstCam[i][FLAGUN] = 1'b1;
              if (LockedRead | LockedWrite)
                WBurstCam[i][FLAGLO] = 1'b1;
            end
            `AXI_AUX_ST_LOCKED :
            begin
              if (UnlockedRead | UnlockedWrite)
                WBurstCam[i][FLAGUN] = 1'b1;
              if (LockedRead | LockedWrite)
                WBurstCam[i][FLAGLO] = 1'b1;
            end
            `AXI_AUX_ST_LOCK_LAST :
            begin
              if (UnlockedRead | UnlockedWrite)
                WBurstCam[i][FLAGLL] = 1'b1;
              if (LockedRead | LockedWrite)
                WBurstCam[i][FLAGLO] = 1'b1;
            end
            `AXI_AUX_ST_NOT_USED :
              ; // Unreachable, don't-care
            default : ; // Unreachable, don't-care
          endcase // case (LockState)
        end
      end

      // Check for an empty WAddrCam, clearing the nWAddrTrans flag
      // if any write addresses are present
      // Update the flags indicating if WBurstCam contains locked/unlocked
      // transactions and bus state flags
      nWAddrTrans    <= 1'b1;
      UnlockedInWCam <= 1'b0;
      LockedInWCam   <= 1'b0;
      FlagUNInWCam   <= 1'b0;
      FlagLOInWCam   <= 1'b0;
      FlagLLInWCam   <= 1'b0;
      for (i = 1; i <= MAXWBURSTS; i = i+1)
      begin
        if (i < WIndex) // only consider valid entries in WBurstCam
        begin
          if (WBurstCam[i][FLAGUN])
            FlagUNInWCam <= 1'b1;
          if (WBurstCam[i][FLAGLO])
            FlagLOInWCam <= 1'b1;
          if (WBurstCam[i][FLAGLL])
            FlagLLInWCam <= 1'b1;
          if (WAddrCam[i])
          begin
            nWAddrTrans <= 1'b0;
            if (WBurstCam[i][LOCKED])
              LockedInWCam <= 1'b1;
            else
              UnlockedInWCam <= 1'b1;
          end
        end
      end

    end // else: !if(!`AXI_AUX_RSTn)
  end // always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)

  // Combine cam flags with current bus state to drive the flags
  // indicating which types of lock write transactions are present
  // on the bus (if any)
  assign LockedWrite   = LockedInWCam ||
                        (AWVALID && (AWLOCK == `AXI_ALOCK_LOCKED));
  assign UnlockedWrite = UnlockedInWCam ||
                        (AWVALID && (AWLOCK != `AXI_ALOCK_LOCKED));

  assign StrbError = AWStrbError | BStrbError;

  assign WriteDataNumError = AWDataNumError | WDataNumError;


  // INDEX:        - Write Depth array
  // =====
  // Array monitors interleaved write data

  // Lookup table for IDs used by the exclusive access monitor
  // Each location in the table has a valid flag to indicate if the ID is in use
  always @(negedge `AXI_AUX_RSTn or posedge `AXI_AUX_CLK)
  begin : p_WdepthIdSeq
    integer i;  // loop counter
    if (!`AXI_AUX_RSTn)
    begin
      WdepthIdValid <= {WDEPTH+1{1'b0}};
      WdepthIdDelta <= 1'b0;
      for (i = 0; i <= WDEPTH; i = i + 1)
      begin
        WdepthId[i] <= {ID_WIDTH{1'b0}};
      end
    end
    else // clk edge
    begin
      // write transfer
      if (WVALID && WREADY &&
          !WdepthIdFull)
      begin
        WdepthId[WdepthIdWrPtr] <= WID;
        WdepthIdValid[WdepthIdWrPtr] <= !WLAST;
        WdepthIdDelta <= ~WdepthIdDelta;
      end
    end // else: !if(!`AXI_AUX_RSTn)
  end // block: p_WdepthIdSeq

  // Lookup table is full when all valid bits are set
  assign WdepthIdFull = &WdepthIdValid;

  // New IDs are written to the highest location
  // that does not have the valid flag set 
  always @(WdepthIdValid or WdepthIdDelta)
  begin : p_WdepthIdFreePtrComb
    integer i;  // loop counter
    WdepthIdFreePtr = 0;
    for (i = 0; i <= WDEPTH; i = i + 1)
    begin
      if (WdepthIdValid[i] == 1'b0)
      begin
        WdepthIdFreePtr = i;
      end
    end
  end // p_WdepthIdFreePtrComb

  // If the ID is already being monitored then reuse the location
  // New IDs are written to the highest location
  // that does not have the valid flag set 
  assign WdepthIdWrPtr = WdepthWMatch ? WdepthWId : WdepthIdFreePtr;

  // Write address ID comparator
  always @(WVALID or WID or WdepthIdValid or WdepthIdDelta)
  begin : p_WdepthWMatchComb
    integer i;  // loop counter
    WdepthWMatch = 1'b0;
    WdepthWId = {WDEPTH+1{1'b0}};
    if (WVALID)
    begin
      for (i = 0; i <= WDEPTH; i = i + 1)
      begin
        if (WdepthIdValid[i] && (WID == WdepthId[i]))
        begin
          WdepthWMatch = 1'b1;
          WdepthWId = i;
        end
      end
    end
  end // p_WdepthWMatchComb

  // Sum the bits from the WidInUse register to give the current write depth
  always @(WdepthIdValid or WdepthWMatch or WVALID)
  begin : p_WidDepthComb
    integer id; // loop counter
    WidDepth = 0;
    for (id = 0; id <= WDEPTH; id = id + 1)
    begin
      if (WdepthIdValid[id] == 1'b1)
      begin
        WidDepth = 1 + WidDepth;
      end
    end
    // Add one if a new WID is in use
    if (WVALID && !WdepthWMatch)
    begin
      WidDepth = WidDepth + 1'b1;
    end
  end // p_WidDepthComb


//------------------------------------------------------------------------------
// INDEX:   5) Verilog Functions
//------------------------------------------------------------------------------


  // INDEX:        - CheckBurst
  // =====
  // Inputs: Burst (burst data structure)
  //         Count (number of data items)
  // Returns: High is any of the write strobes are illegal
  // Calls CheckStrb to test each WSTRB value.
  //------------------------------------------------------------------------------
  function CheckBurst;
    input [WBURSTMAX:0] Burst;         // burst vector
    input         [5:0] Count;         // number of beats in the burst
    integer             loop;          // general loop counter
    integer             NumBytes;      // number of bytes in the burst
    reg           [6:0] StartAddr;     // start address of burst
    reg           [6:0] StrbAddr;      // address used to check WSTRB
    reg           [2:0] StrbSize;      // size used to check WSTRB
    reg           [3:0] StrbLen;       // length used to check WSTRB
    reg    [STRB_MAX:0] Strb;          // WSTRB to be checked
    reg           [9:0] WrapMaskWide;  // address mask for wrapping bursts
    reg           [6:0] WrapMask;      // relevant bits WrapMaskWide
  begin

    StartAddr   = Burst[ADDRHI:ADDRLO];
    StrbAddr    = StartAddr; // incrementing address initialises to start addr
    StrbSize    = Burst[ASIZEHI:ASIZELO];
    StrbLen     = Burst[ALENHI:ALENLO];
    CheckBurst  = 1'b0;

    // Initialize to avoid latch warnings (not really latches as they are set in loop)
    Strb         = {STRB_WIDTH{1'bX}};
    WrapMask     =          {7{1'bX}};
    WrapMaskWide =         {10{1'bX}};

    // determine the number of bytes in the burst for wrapping purposes
    NumBytes = (StrbLen + 1) << StrbSize;

    // Check the strobe for each write data transfer
    for (loop=1; loop<=16; loop=loop+1)
    begin
      if (loop <= Count) // Only consider entries up to burst length
      begin

        // Need to use full case statement to index WSTRB as in Verilog the
        // bit slice range must be bounded by constant expressions
        case (loop)
          1  : Strb = Burst[STRB1HI:STRB1LO];
          2  : Strb = Burst[STRB2HI:STRB2LO];
          3  : Strb = Burst[STRB3HI:STRB3LO];
          4  : Strb = Burst[STRB4HI:STRB4LO];
          5  : Strb = Burst[STRB5HI:STRB5LO];
          6  : Strb = Burst[STRB6HI:STRB6LO];
          7  : Strb = Burst[STRB7HI:STRB7LO];
          8  : Strb = Burst[STRB8HI:STRB8LO];
          9  : Strb = Burst[STRB9HI:STRB9LO];
          10 : Strb = Burst[STRB10HI:STRB10LO];
          11 : Strb = Burst[STRB11HI:STRB11LO];
          12 : Strb = Burst[STRB12HI:STRB12LO];
          13 : Strb = Burst[STRB13HI:STRB13LO];
          14 : Strb = Burst[STRB14HI:STRB14LO];
          15 : Strb = Burst[STRB15HI:STRB15LO];
          16 : Strb = Burst[STRB16HI:STRB16LO];
          default : Strb = {STRB_WIDTH{1'bx}};
        endcase

        // returns high if any strobes are illegal
        if (CheckStrb(StrbAddr, StrbSize, Strb))
        begin
          CheckBurst = 1'b1;
        end

        // -----------------------------------------------------------------------
        // Increment aligned StrbAddr
        if (Burst[BURSTHI:BURSTLO] != `AXI_ABURST_FIXED)
          // fixed bursts don't increment or align the address
        begin
          // align and increment address,
          // Address is incremented from an aligned version
          StrbAddr = StrbAddr &
            (7'b111_1111 - (7'b000_0001 << StrbSize) + 7'b000_0001);
                                                                // align to size
          StrbAddr = StrbAddr + (7'b000_0001 << StrbSize);      // increment
        end // if (Burst[BURSTHI:BURSTLO] != `AXI_ABURST_FIXED)

        // for wrapping bursts the top bits of the strobe address remain fixed
        if (Burst[BURSTHI:BURSTLO] == `AXI_ABURST_WRAP)
        begin
          WrapMaskWide = (10'b11_1111_1111 - NumBytes + 10'b00_0000_0001);
                                            // To wrap the address, need 10 bits
          WrapMask = WrapMaskWide[6:0];
                    // Only 7 bits of address are necessary to calculate strobe
          StrbAddr = (StartAddr & WrapMask) | (StrbAddr & ~WrapMask);
                // upper bits remain stable for wrapping bursts depending on the
                // number of bytes in the burst
        end
      end // if (loop < Count)
    end // for (loop=1; loop<=WDEPTH; loop=loop+1)
  end
  endfunction // CheckBurst


  // INDEX:        - CheckStrb
  // =====
  function CheckStrb;
    input        [6:0] StrbAddr;
    input        [2:0] StrbSize;
    input [STRB_MAX:0] Strb;
    reg   [STRB_MAX:0] StrbMask;
  begin

    // The basic strobe for an aligned address
    StrbMask = (STRB_1 << (STRB_1 << StrbSize)) - STRB_1;

    // Zero the unaligned byte lanes
    // Note: the number of unaligned byte lanes is given by:
    // (StrbAddr & ((1 << StrbSize) - 1)), i.e. the unaligned part of the
    // address with respect to the transfer size
    //
    // Note! {{STRB_MAX{1'b0}}, 1'b1} gives 1 in the correct vector length

    StrbMask = StrbMask &                   // Mask off unaligned byte lanes
      (StrbMask <<                          // shift the strb mask left by
        (StrbAddr & ((STRB_1 << StrbSize) -  STRB_1))
                                            // the number of unaligned byte lanes
      );

    // Shift mask into correct byte lanes
    // Note: (STRB_MAX << StrbSize) & STRB_MAX is used as a mask on the address
    // to pick out the bits significant bits, with respect to the bus width and
    // transfer size, for shifting the mask to the correct byte lanes.
    StrbMask = StrbMask << (StrbAddr & ((STRB_MAX << StrbSize) & STRB_MAX));

    // check for strobe error
    CheckStrb = (|(Strb & ~StrbMask));

  end
  endfunction // CheckStrb


  // INDEX:        - ReadDataMask
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Read data mask for valid byte lanes.
  //------------------------------------------------------------------------------
  function [DATA_MAX:0] ReadDataMask;
    input [STRB16HI:0] Burst;         // burst vector
    input [5:0]        Beat;          // beat number in the burst (0-15)
    reg   [11:0] bit_count;
    reg   [DATA_MAX+1:0] byte_mask;
  begin
    bit_count = ByteCount(Burst, Beat) << 3;
    byte_mask = (1'b1 << bit_count) - 1;
    // Result is the valid byte mask shifted by the calculated bit shift
    ReadDataMask = byte_mask[DATA_MAX:0] << (ByteShift(Burst, Beat)*8);
  end
  endfunction // ReadDataMask


  // INDEX:        - ByteShift
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Byte Shift for valid byte lanes.
  //------------------------------------------------------------------------------
  function [DATA_MAX:0] ByteShift;
    input [STRB16HI:0] Burst;         // burst vector
    input [5:0]        Beat;          // beat number in the burst (0-15)
    reg   [6:0]        axaddr;
    reg   [2:0]        axsize;
    reg   [3:0]        axlen;
    reg   [1:0]        axburst;
    integer bus_data_bytes;
    integer length;
    integer unaligned_byte_shift;
    integer beat_addr_inc;
    integer addr_trans_bus;
    integer addr_trans_bus_inc;
    integer wrap_point;
    integer transfer_byte_shift;
  begin
    axaddr  = Burst[ADDRHI:ADDRLO];
    axsize  = Burst[ASIZEHI:ASIZELO];
    axlen   = Burst[ALENHI:ALENLO];
    axburst = Burst[BURSTHI:BURSTLO];

    bus_data_bytes = STRB_WIDTH;

    length = axlen + 1;

    // Number of bytes that the data needs to be shifted when
    // the address is unaligned
    unaligned_byte_shift =
      axaddr &               // Byte address
      ((1<<axsize)-1);       //   masked by the number of bytes
                             //   in a transfer

    // Burst beat address increment
    beat_addr_inc = 0;
    // For a FIXED burst ther is no increment
    // For INCR and WRAP it is the beat number minus 1
    if (axburst != 0)
    begin
      beat_addr_inc = Beat;
    end

    // Transfer address within data bus
    // The root of the transfer address within the data bus is byte address
    // divided by the number of bytes in each transfer. This is also masked
    // so that the upper bits that do not control the byte shift are not
    // included.
    addr_trans_bus = (axaddr & (bus_data_bytes - 1))>>axsize;

    // The address may increment with each beat. The increment will be zero
    // for a FIXED burst.
    addr_trans_bus_inc = addr_trans_bus + beat_addr_inc;

    // Modify the byte shift for wrapping bursts
    if (axburst == 2)
    begin
      // The upper address of the transfer before wrapping
      wrap_point = length + (addr_trans_bus & ~(length - 1));
      // If adding the beat number to the transfer address causes it to
      // pass the upper wrap address then wrap to the lower address.
      if (addr_trans_bus_inc >= wrap_point)
      begin
        addr_trans_bus_inc = addr_trans_bus_inc - length;
      end
    end

    // Address calculation may exceed the number of transfers that can fit
    // in the data bus for INCR bursts. So the calculation is truncated to
    // make the byte shift wrap round to zero. 
    addr_trans_bus_inc = addr_trans_bus_inc & ((bus_data_bytes-1)>>axsize);

    // Number of bytes that the data needs to be shifted when
    // the transfer size is less than the data bus width
    transfer_byte_shift = (1<<axsize) *     // Number of bytes in a transfer
                          addr_trans_bus_inc;// Transfer address within data bus

    // For a FIXED burst or on the frist beat of an INCR burst
    // shift the data if the address is unaligned
    if ((axburst == 0) || ((axburst == 1) && (Beat == 0)))
    begin
      ByteShift = transfer_byte_shift + unaligned_byte_shift;
    end
    else
    begin
      ByteShift = transfer_byte_shift;
    end
  end
  endfunction // ByteShift


  // INDEX:        - ByteCount
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Byte Count of valid byte lanes.
  //------------------------------------------------------------------------------
  function [7:0] ByteCount;
    input [STRB16HI:0] Burst;         // burst vector
    input [5:0]        Beat;          // beat number in the burst (0-15)
    reg   [6:0]        axaddr;
    reg   [2:0]        axsize;
    reg   [3:0]        axlen;
    reg   [1:0]        axburst;
    integer bus_data_bytes;
    integer unaligned_byte_shift;
  begin
    axaddr  = Burst[ADDRHI:ADDRLO];
    axsize  = Burst[ASIZEHI:ASIZELO];
    axlen   = Burst[ALENHI:ALENLO];
    axburst = Burst[BURSTHI:BURSTLO];

    bus_data_bytes = STRB_WIDTH;

    // Number of bytes that the data needs to be shifted when
    // the address is unaligned
    unaligned_byte_shift =
      axaddr &              // Byte address
      ((1<<axsize)-1);      //   masked by the number of bytes
                            //   in a transfer

    // The number of valid bits depends on the transfer size.
    ByteCount = (1<<axsize);

    // For FIXED bursts or on the first beat of an INCR burst
    // if the address is unaligned modify the number of
    // valid strobe bits
    if ((axburst == 0) || (Beat == 0))
    begin
      // The number of valid bits depends on the transfer size
      // and the offset of the unaligned address.
      ByteCount = ByteCount - unaligned_byte_shift;
    end
  end
  endfunction // ByteCount


//------------------------------------------------------------------------------
// INDEX:
// INDEX: End of File
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// INDEX:   1) Clear Verilog Defines
//------------------------------------------------------------------------------

  // Lock FSM States (3-state FSM, so one state encoding is not used)
  `undef AXI_AUX_ST_UNLOCKED
  `undef AXI_AUX_ST_LOCKED
  `undef AXI_AUX_ST_LOCK_LAST
  `undef AXI_AUX_ST_NOT_USED

  // Clock and Reset
  `undef AXI_AUX_CLK
  `undef AXI_SVA_CLK
  `undef AXI_AUX_RSTn
  `undef AXI_SVA_RSTn

  // Others
  `undef AXI_ANTECEDENT
  `undef AXI_END_OF_SIMULATION
  `undef AXI_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:   2) End of module
//------------------------------------------------------------------------------

endmodule // AxiPC
