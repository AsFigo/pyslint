//Source: https://github.com/openhwgroup/core-v-verif/blob/2dd5594be3f81c3f58f677a6ccbabeee388e90ee/cv32e40x/env/uvme/cov/uvme_debug_covg.sv#L158
//
///////////////////////////////////////////////////////////////////////////////
// Copyright 2020 OpenHW Group
// Copyright 2020 BTA Design Services
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////


`define per_instance_fcov option.per_instance = 1;

module uvme_debug_covg;


    /*
    * Covergroups
    */
bit  cntxt_ctrl_fsm_cs;
bit  cntxt_is_ebreak ;
bit  cntxt_dcsr_q_15 ;
bit  cntxt_debug_mode_q ;
bit  cntxt_is_cebreak ;
bit  cntxt_dcsr_q_2 ;
bit  cntxt_tdata1_2 ;
bit  cntxt_trigger_match_in_wb ;
bit  cntxt_addr_match ;
bit  cntxt_illegal_insn_i;
bit  cntxt_sys_ecall_insn_i ;
bit  [8:0] cntxt_irq_i ;
bit  cntxt_is_wfi ;
bit  cntxt_in_wfi ;
bit  cntxt_debug_req_i ;
bit  cntxt_dpc_will_hit ;
bit  cntxt_dcsr_q_11;
bit  cntxt_is_dret ;
bit  cntxt_branch_in_ex ;
bit  cntxt_is_mulhsu ;
bit  cntxt_csr_access;
bit  cntxt_wb_valid;
bit  cntxt_csr_op ;
bit  cntxt_wb_stage_instr_rdata_i_31_20 ; // csr addr not updated if illegal access
bit  cntxt_mcountinhibit_q_0;
bit  cntxt_mcountinhibit_q_2;
bit  cntxt_sys_fence_insn_i ;

  covergroup cg_debug_mode_ext ;
          `per_instance_fcov
          state: coverpoint cntxt_ctrl_fsm_cs{
          }
  endgroup : cg_debug_mode_ext

  // Cover that we execute ebreak with dcsr.ebreakm==1
  covergroup cg_ebreak_execute_with_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt_is_ebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt_dcsr_q_15 {
                  bins active = {1};
          }
          dm : coverpoint cntxt_debug_mode_q {
                  bins active = {1};
          }
          ebreak_with_ebreakm: cross ex, ebreakm_set;
          ebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute c.ebreak with dcsr.ebreakm==1
  covergroup cg_cebreak_execute_with_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt_is_cebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt_dcsr_q_15 {
                  bins active = {1};
          }
          dm : coverpoint cntxt_debug_mode_q {
                  bins active = {1};
          }
          cebreak_with_ebreakm: cross ex, ebreakm_set;
          cebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==0
  covergroup cg_ebreak_execute_without_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt_is_ebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt_dcsr_q_15 {
                  bins active = {0};
          }
          step: coverpoint cntxt_dcsr_q_2 {
                  bins active = {1};
          }
          nostep: coverpoint cntxt_dcsr_q_2 {
                  bins active = {0};
          }
          ebreak_regular_nodebug: cross ex, ebreakm_clear, nostep;
          ebreak_step_nodebug : cross ex, ebreakm_clear, step;
  endgroup

  // Cover that we execute c.ebreak with dcsr.ebreakm==0
  covergroup cg_cebreak_execute_without_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt_is_cebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt_dcsr_q_15 {
                  bins active = {0};
          }
          step: coverpoint cntxt_dcsr_q_2 {
                  bins active = {1};
          }
          nostep: coverpoint cntxt_dcsr_q_2 {
                  bins active = {0};
          }
          cebreak_regular_nodebug: cross ex, ebreakm_clear, nostep;
          cebreak_step_nodebug : cross ex, ebreakm_clear, step;
  endgroup

    // Cover that we hit a trigger match
    covergroup cg_trigger_match;
        `per_instance_fcov
        en : coverpoint cntxt_tdata1_2 {
            bins active = {1};
        }
        match: coverpoint cntxt_trigger_match_in_wb {
            //TODO:ropeders should use the wb_valid-qualified "is_trigger_match"?
            bins hit = {1};
        }
        ok_match: cross en, match;
    endgroup

    // cover that we hit pc==tdata2  without having enabled trigger in m/d-mode
    // cover hit in d-mode with trigger enabled (no action)
    covergroup cg_trigger_match_disabled;
        `per_instance_fcov
        dis : coverpoint cntxt_tdata1_2 {
            bins hit = {0};
        }
        en : coverpoint cntxt_tdata1_2 {
            bins hit = {1};
        }
        match: coverpoint cntxt_addr_match {
           bins hit = {1};
        }
        mmode : coverpoint cntxt_debug_mode_q {
           bins m = {0};
        }
        dmode : coverpoint cntxt_debug_mode_q {
           bins m = {1};
        }
        m_match_without_en : cross dis, match, mmode;
        d_match_without_en : cross dis, match, dmode;
        d_match_with_en    : cross en, match, dmode;
    endgroup

    // Cover that we hit an exception during debug mode
    covergroup cg_debug_mode_exception;
        `per_instance_fcov
        dm : coverpoint cntxt_debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint (cntxt_illegal_insn_i && cntxt_wb_valid) {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we hit an ecall during debug mode
    covergroup cg_debug_mode_ecall;
        `per_instance_fcov
        dm : coverpoint cntxt_debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint cntxt_sys_ecall_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we get interrupts while in debug mode
    covergroup cg_irq_in_debug;
        `per_instance_fcov
        dm : coverpoint cntxt_debug_mode_q {
            bins hit  = {1};
        }
        irq : coverpoint |cntxt_irq_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, irq;
    endgroup

    // Cover that hit a WFI insn in debug mode
    covergroup cg_wfi_in_debug;
        `per_instance_fcov
        iswfi : coverpoint cntxt_is_wfi {
                bins hit  = {1};
        }
        dm : coverpoint cntxt_debug_mode_q {
            bins hit = {1};
        }
        dm_wfi : cross iswfi, dm;
    endgroup

    // Cover that we get a debug_req while in wfi
    covergroup cg_wfi_debug_req;
        `per_instance_fcov
        inwfi : coverpoint cntxt_in_wfi {
                bins hit  = {1};
        }
        dreq: coverpoint cntxt_debug_req_i {
            bins hit = {1};
        }
        dm_wfi : cross inwfi, dreq;
    endgroup

    // Cover that we perform single stepping
    covergroup cg_single_step;
        `per_instance_fcov
        step : coverpoint cntxt_dcsr_q_2 {
                bins en  = {1};
        }
        mmode: coverpoint cntxt_debug_mode_q {
            bins hit = {0};
        }
        trigger : coverpoint cntxt_trigger_match_in_wb {
            bins hit = {1};
        }
        wfi : coverpoint cntxt_is_wfi {
            bins hit = {1};
        }
        ill : coverpoint (cntxt_illegal_insn_i && cntxt_wb_valid) {
            bins hit = {1};
        }
        pc_will_trig : coverpoint cntxt_dpc_will_hit {
            bins hit = {1};
        }
        stepie : coverpoint cntxt_dcsr_q_11;
        mmode_step : cross step, mmode;
        mmode_step_trigger_match : cross step, mmode, trigger;
        mmode_step_wfi : cross step, mmode, wfi;
        mmode_step_stepie : cross step, mmode, stepie;
        mmode_step_illegal : cross step, mmode, ill;
        mmode_step_next_pc_will_match : cross step, mmode, pc_will_trig;
    endgroup

    // Cover dret is executed in machine mode
    covergroup cg_mmode_dret;
        `per_instance_fcov
        mmode : coverpoint cntxt_debug_mode_q;
        dret_ins : coverpoint cntxt_is_dret {
            bins hit = {1};
        }
        dret_ex : cross mmode, dret_ins;
    endgroup

    // Cover debug_req and irq asserted on same cycle
    covergroup cg_irq_dreq;
        `per_instance_fcov
        dreq : coverpoint cntxt_debug_req_i {
                bins trans_active  = (1'b0 => 1'b1);
        }
        irq  : coverpoint |cntxt_irq_i {
                bins trans_active = (1'b0 => 1'b1);
        }
        trigger : coverpoint cntxt_trigger_match_in_wb {
            bins hit = {1};
        }
        ill : coverpoint (cntxt_illegal_insn_i && cntxt_wb_valid) {
            bins hit = {1};
        }
        ebreak : coverpoint cntxt_is_ebreak {
            bins active= {1'b1};
        }
        cebreak : coverpoint cntxt_is_cebreak {
            bins active= {1'b1};
        }
        branch : coverpoint cntxt_branch_in_ex {
            bins active= {1'b1};
        }
        mulhsu : coverpoint cntxt_is_mulhsu {
            bins active= {1'b1};
        }
        dreq_and_ill : cross dreq, ill;
        irq_and_dreq : cross dreq, irq;
        irq_dreq_trig_ill : cross dreq, irq, trigger, ill;
        irq_dreq_trig_cebreak : cross dreq, irq, trigger, cebreak;
        irq_dreq_trig_ebreak : cross dreq, irq, trigger, ebreak;
        irq_dreq_trig_branch : cross dreq, irq, trigger, branch;
        irq_dreq_trig_multicycle : cross dreq, irq, trigger, mulhsu;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1 in D-mode
    covergroup cg_debug_regs_d_mode;
        `per_instance_fcov
        mode : coverpoint cntxt_debug_mode_q {
            bins M = {1};
        }
        access : coverpoint (cntxt_csr_access && cntxt_wb_valid) {
            bins hit = {1};
        }
        op : coverpoint cntxt_csr_op {
            bins read = {'h0};
            bins write = {'h1};
            // TODO:ropeders also SET and CLEAR?
        }
        addr : coverpoint cntxt_wb_stage_instr_rdata_i_31_20 { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op, addr;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1 in M-mode
    covergroup cg_debug_regs_m_mode;
        `per_instance_fcov
        mode : coverpoint cntxt_debug_mode_q {
            bins M = {0};
        }
        access : coverpoint (cntxt_csr_access && cntxt_wb_valid) {
            bins hit = {1};
        }
        op : coverpoint cntxt_csr_op {
            bins read = {1'h0};
            bins write = {1'h1};
            // TODO:ropeders also SET and CLEAR?
        }
        addr : coverpoint cntxt_wb_stage_instr_rdata_i_31_20 { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op, addr;
    endgroup

    // Cover access to trigger registers
    // TODO Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_trigger_regs;
        `per_instance_fcov
        mode : coverpoint cntxt_debug_mode_q; // Only M and D supported
        access : coverpoint (cntxt_csr_access && cntxt_wb_valid) {
            bins hit = {1};
        }
        op : coverpoint cntxt_csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr : coverpoint cntxt_wb_stage_instr_rdata_i_31_20 { // csr addr not updated if illegal access
            bins tsel = {'h7A0};
            bins tdata1 = {'h7A1};
            bins tdata2 = {'h7A2};
            bins tdata3 = {'h7A3};
            bins tinfo  = {'h7A4};
        }
        tregs_access : cross mode, access, op, addr;
    endgroup

    // Cover that we run with counters mcycle and minstret enabled
    covergroup cg_counters_enabled;
        `per_instance_fcov
        mcycle_en : coverpoint cntxt_mcountinhibit_q_0;
        minstret_en : coverpoint cntxt_mcountinhibit_q_2;
    endgroup

    // Cover that we get a debug_req_i while in RESET state
    covergroup cg_debug_at_reset;
        `per_instance_fcov
        state : coverpoint cntxt_ctrl_fsm_cs {
            bins reset= {1};
        }
         dbg : coverpoint cntxt_debug_req_i {
            bins active= {1'b1};
        }
        dbg_at_reset : cross state, dbg;
    endgroup

    // Cover that we execute fence and fence.i in debug mode
    covergroup cg_fence_in_debug;
        `per_instance_fcov
        mode : coverpoint cntxt_debug_mode_q {
            bins debug= {1'b1};
        }
        fence : coverpoint cntxt_sys_fence_insn_i {
            bins active= {1'b1};
        }
        fence_in_debug : cross mode, fence;
    endgroup

    // Cover that we get all combinations of debug causes
    covergroup cg_debug_causes;
        `per_instance_fcov
        tmatch : coverpoint cntxt_trigger_match_in_wb {
            bins match= {1'b1};
        }
        tnomatch : coverpoint cntxt_trigger_match_in_wb {
            bins nomatch= {1'b0};
        }
         ebreak : coverpoint cntxt_is_ebreak {
            bins active= {1'b1};
        }
         cebreak : coverpoint cntxt_is_cebreak {
            bins active= {1'b1};
        }
         dbg_req : coverpoint cntxt_debug_req_i {
            bins active= {1'b1};
        }
         step : coverpoint cntxt_dcsr_q_2 & !cntxt_debug_mode_q {
            bins active= {1'b1};
        }
        trig_vs_ebreak : cross tmatch, ebreak;
        trig_vs_cebreak : cross tmatch, cebreak;
        trig_vs_dbg_req : cross tmatch, dbg_req;
        trig_vs_step : cross tmatch, step;
        // Excluding trigger match to check 'lower' priority causes
        ebreak_vs_req : cross ebreak, dbg_req, tnomatch;
        cebreak_vs_req : cross cebreak, dbg_req, tnomatch;
        ebreak_vs_step : cross ebreak, step;
        cebreak_cs_step : cross cebreak, step;
        dbg_req_vs_step : cross dbg_req, step;
    endgroup

endmodule : uvme_debug_covg

