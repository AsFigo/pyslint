# PySlint
SystemVerilog Linter based on pyslang

# Update 08-Nov-2023
Quick update on the latest rules made available in the public repo:

 * NAME_INTF_SUFFIX
 * NAME_CLASS_SUFFIX
 * NAME_CNST_SUFFIX
 * NAME_CG_PREFIX
 * NAME_CP_PREFIX
 * NAME_CR_PREFIX
 * NAME_PROP_PREFIX
 * NAME_AST_PREFIX
 * NAME_ASM_PREFIX
 * NAME_COV_PREFIX
 * SVA_MISSING_FAIL_AB
 * SVA_MISSING_LABEL
 * SVA_MISSING_ENDLABEL
 * SVA_NO_PASS_AB
 * COMPAT_SVA_NO_CONC_IN_FE
 * COMPAT_DPI_OLD_SPECSTR
 * CL_METHOD_NOT_EXTERN
 * CL_MISSING_ENDLABEL
 * PERF_CG_TOO_MANY_CROSS
 * FUNC_CNST_MISSING_CAST
 * FUNC_CNST_DIST_COL_EQ
 * REUSE_NO_TDEF_IN_MOD
 * COMPAT_CG_OPT_PI_CL
 * REUSE_CG_NO_ILBINS_CL
 * REUSE_NO_WILDC_AA_CL
 * PERF_CG_NO_ABIN_W_DEF_CL
 * COMPAT_SVA_NO_DEGEN_CONSEQ
 * REUSE_ONE_CL_PER_FILE
 * REUSE_ONE_MOD_PER_FILE


# Update 10-May-2023

## Very Important note on use model
Whole lot is expected to change, so please do NOT use this in production just yet, but you can defintely get motivated from the apporach/API and implement in your own work (or even better, call us for custom deployment!).

* First few rules added

## Run examples
* cd exec_dir
* make

## Rules added so far (May 17 2023)
* CL_METHOD_NOT_EXTERN
* NAME_CG_PREFIX
* NAME_CG_PREFIX
* SVA_MISSING_LABEL
* NAME_AST_PREFIX
* SVA_MISSING_LABEL
* NAME_ASM_PREFIX
* SVA_MISSING_LABEL
* NAME_COV_PREFIX
* NAME_PROP_PREFIX
* SVA_MISSING_ENDLABEL
* SVA_NO_PASS_AB
* SVA_MISSING_FAIL_AB
* CL_MISSING_ENDLABEL

## Dependencies
* pyslang
* make
* Python 3.xx

## New rules
* Please open new issue for every new rule with detailed explanation and a short test

