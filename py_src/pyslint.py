# ----------------------------------------------------
# SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
#                         AsFigo Technologies, UK
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

import pyslang
import argparse
import tomli
import copy
import functools
from operator import countOf
import operator as op

print_verbose = False

def pyslint_update_rule_ids():
  lv_sv_ruleid_l = list()
  lv_sv_ruleid_l.append('CL_METHOD_NOT_EXTERN')
  lv_sv_ruleid_l.append('VLT_NO_GENERIC_MBX')
  lv_sv_ruleid_l.append('VLT_NO_CB_IN_INTF')
  lv_sv_ruleid_l.append('NAME_INTF_SUFFIX')
  lv_sv_ruleid_l.append('NAME_CLASS_SUFFIX')
  lv_sv_ruleid_l.append('NAME_CNST_SUFFIX')
  lv_sv_ruleid_l.append('NAME_CG_PREFIX')
  lv_sv_ruleid_l.append('NAME_CP_PREFIX')
  lv_sv_ruleid_l.append('NAME_CR_PREFIX')
  lv_sv_ruleid_l.append('NAME_PROP_PREFIX')
  lv_sv_ruleid_l.append('NAME_AST_PREFIX')
  lv_sv_ruleid_l.append('NAME_ASM_PREFIX')
  lv_sv_ruleid_l.append('NAME_COV_PREFIX')
  lv_sv_ruleid_l.append('FUNC_SVA_MISSING_FAIL_AB')
  lv_sv_ruleid_l.append('DBG_SVA_MISSING_LABEL')
  lv_sv_ruleid_l.append('DBG_SVA_MISSING_ENDLABEL')
  lv_sv_ruleid_l.append('PERF_SVA_NO_PASS_AB')
  lv_sv_ruleid_l.append('COMPAT_SVA_NO_CONC_IN_FE')
  lv_sv_ruleid_l.append('COMPAT_SVA_NO_EXPECT_EXPR_IN_INIT')
  lv_sv_ruleid_l.append('COMPAT_DPI_OLD_SPECSTR')
  lv_sv_ruleid_l.append('COMPAT_DPI_NO_PURE_TASK')
  lv_sv_ruleid_l.append('FUNC_NO_2STATE_IN_INTF')
  lv_sv_ruleid_l.append('FUNC_DPI_FN_MISSING_RTYPE')
  lv_sv_ruleid_l.append('FUNC_DPI_NO_4STATE_IN_RETURN')
  lv_sv_ruleid_l.append('FUNC_DPI_NO_4STATE_IN_ARGS')
  lv_sv_ruleid_l.append('FUNC_NO_BEGIN_IN_TIMING_CTRL')
  lv_sv_ruleid_l.append('DBG_AVOID_BEGIN_IN_TASK')
  lv_sv_ruleid_l.append('DBG_AVOID_BEGIN_IN_FN')
  lv_sv_ruleid_l.append('FUNC_NO_INIT_OF_STATIC_VAR_IN_SFN')
  lv_sv_ruleid_l.append('COMPAT_VAR_DINIT_IN_SFN')
  lv_sv_ruleid_l.append('COMPAT_NO_REF_IN_STATIC_FN')
  lv_sv_ruleid_l.append('COMPAT_DPI_NO_MDA')
  lv_sv_ruleid_l.append('DBG_CL_MISSING_ENDLABEL')
  lv_sv_ruleid_l.append('COMPAT_PRE_RAND_NON_VOID')
  lv_sv_ruleid_l.append('COMPAT_POST_RAND_NON_VOID')
  lv_sv_ruleid_l.append('PERF_CG_TOO_MANY_CROSS')
  lv_sv_ruleid_l.append('FUNC_CNST_MISSING_CAST')
  lv_sv_ruleid_l.append('FUNC_CNST_WRONG_OPER_PRI')
  lv_sv_ruleid_l.append('FUNC_CNST_DIST_COL_EQ')
  lv_sv_ruleid_l.append('REUSE_NO_TDEF_IN_MOD')
  lv_sv_ruleid_l.append('COMPAT_CG_OPT_PI_CL')
  lv_sv_ruleid_l.append('REUSE_CG_NO_ILBINS_CL')
  lv_sv_ruleid_l.append('REUSE_NO_WILDC_AA_CL')
  lv_sv_ruleid_l.append('PERF_CG_NO_ABIN_W_DEF_CL')
  lv_sv_ruleid_l.append('COMPAT_SVA_NO_DEGEN_CONSEQ')
  lv_sv_ruleid_l.append('COMPAT_SVA_PROP_MISSING_SEMI')
  lv_sv_ruleid_l.append('COMPAT_SVA_NO_DEGEN_AST')
  lv_sv_ruleid_l.append('COMPAT_SVA_NO_S_UNTIL_WITH')
  lv_sv_ruleid_l.append('REUSE_ONE_CL_PER_FILE')
  lv_sv_ruleid_l.append('REUSE_ONE_MOD_PER_FILE')
  lv_sv_ruleid_l.append ('DBG_SVA_AST_MISSING_LABEL')
  lv_sv_ruleid_l.append ('DBG_SVA_ASM_MISSING_LABEL')
  lv_sv_ruleid_l.append ('DBG_SVA_COV_MISSING_LABEL')

'''
with open("cfg.toml", mode="rb") as fp:
  config = tomli.load(fp)
  #print(config)
'''

def pyslint_rule_enabled(rule_id):
  return True

def pyslint_msg(rule_id, msg):
  if (pyslint_rule_enabled(rule_id)):
    pyslint_str = 'PySlint: Violation: ['
    pyslint_str += rule_id
    pyslint_str += ']: '
    pyslint_str += msg 
    print(pyslint_str)

#PySlint: Error Use extern methods
def CL_METHOD_NOT_EXTERN(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):

      if (cl_item.kind.name == 'ClassMethodDeclaration'):
        if (cl_item.declaration.prototype.name.kind.name != 'ConstructorName'):
            msg = 'method is not declared extern: '+ str(cl_item.declaration.prototype.name)
            lv_rule_id = "CL_METHOD_NOT_EXTERN"
            pyslint_msg(lv_rule_id, msg)

def VLT_NO_GENERIC_MBX(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):

      if (cl_item.kind.name == 'ClassPropertyDeclaration'):
        lv_code_s = str(cl_item)
        lv_cl_prop_s = str(cl_item.declaration.type)
        if (cl_item.declaration.type.kind.name != 'NamedType'):
          continue

        if ( ('mailbox' in lv_cl_prop_s) and
            ('#' not in lv_cl_prop_s)):
          msg = 'A generic mailbox declaration was found. \n'
          msg += '\t While IEEE 1800 LRM allows this, such usage is'
          msg += ' error-prone and harder to debug. \n'
          msg += '\t Verilator does not support this feature.'
          msg += ' Please use typed mailbox such as:'
          msg += ' \'mailbox #(int) in_box;\''
          msg += lv_code_s
          lv_rule_id = "VLT_NO_GENERIC_MBX"
          pyslint_msg(lv_rule_id, msg)


def COMPAT_PRE_RAND_NON_VOID(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):
      if (cl_item.kind.name == 'ClassMethodDeclaration'):
        lv_code_s = cl_item.declaration.prototype.__str__()
        lv_method_name = cl_item.declaration.prototype.name.__str__().strip()

        if (lv_method_name == 'pre_randomize'):
          lv_found_void_rt = False
          if (hasattr(cl_item.declaration.prototype.returnType, 'keyword')):
            lv_ret_type_kw = cl_item.declaration.prototype.returnType.keyword
            lv_ret_type =  lv_ret_type_kw.valueText.strip() 
            if (lv_ret_type == 'void'):
              lv_found_void_rt = True

          if (not lv_found_void_rt):
            msg = 'method pre_randomize not declared as void: '
            msg += '\n\tIEEE 1800 LRM does not'
            msg += ' allow such usage though some tools do compile. \n'
            msg += '\tTo avoid compatibility issues,'
            msg += ' please declare pre_randomize as void function'
            msg += lv_code_s
            lv_rule_id = "COMPAT_PRE_RAND_NON_VOID"
            pyslint_msg(lv_rule_id, msg)

def COMPAT_POST_RAND_NON_VOID(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):
      if (cl_item.kind.name == 'ClassMethodDeclaration'):
        lv_code_s = cl_item.declaration.prototype.__str__()
        lv_method_name = cl_item.declaration.prototype.name.__str__().strip()

        if (lv_method_name == 'post_randomize'):
          lv_found_void_rt = False
          if (hasattr(cl_item.declaration.prototype.returnType, 'keyword')):
            lv_ret_type_kw = cl_item.declaration.prototype.returnType.keyword
            lv_ret_type =  lv_ret_type_kw.valueText.strip() 
            if (lv_ret_type == 'void'):
              lv_found_void_rt = True

          if (not lv_found_void_rt):
            msg = 'method post_randomize not declared as void: '
            msg += '\n\tIEEE 1800 LRM does not'
            msg += ' allow such usage though some tools do compile. \n'
            msg += '\tTo avoid compatibility issues,'
            msg += ' please declare post_randomize as void function'
            msg += lv_code_s
            lv_rule_id = "COMPAT_POST_RAND_NON_VOID"
            pyslint_msg(lv_rule_id, msg)


def FUNC_CNST_DIST_COL_EQ(cnst_i):
  for lv_dist_item_i in cnst_i.expr.distribution.items:
    lv_cnst_expr_s = cnst_i.expr.__str__()
    lv_large_range = False
    if (lv_dist_item_i.kind.name == 'DistItem'):
      if (lv_dist_item_i.range.kind.name == 'OpenRangeExpression'):
        lv_large_range = False
        lv_dist_range_left = int(lv_dist_item_i.range.left.literal.value)
        lv_dist_range_right = int(lv_dist_item_i.range.right.literal.value)
        if (abs(lv_dist_range_right - lv_dist_range_left) > 10):
          lv_large_range = True


      if (lv_dist_item_i.weight.op.kind.name == 'ColonEquals'):
        if (lv_large_range):
          msg  = 'Potentially incorrect constraint expression!'
          msg += ' An expression involving dist ColonEquals if found'
          msg += ' And the range used with ColonEquals is large'
          msg += ' This is likely to skew the random generation'
          msg += ' and prevent other values in the dist expression'
          msg += ' to be generated less-frequently than the large range values'
          msg += ' Review to check if you intended to use ColonSlash'
          msg += ' instead of ColonEquals'
          msg += lv_cnst_expr_s
          lv_rule_id = 'FUNC_CNST_DIST_COL_EQ'
          pyslint_msg(lv_rule_id, msg)

def FUNC_CNST_MISSING_CAST (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):
      if (cl_item.kind.name == 'ConstraintDeclaration'):
        for lv_cnst_i in (cl_item.block.items):
          if (not hasattr(lv_cnst_i, 'expr')):
            continue
          # Fix for Issue 35, Unary expressions
          # do not have left/right
          if (lv_cnst_i.expr.kind.name == 'UnaryLogicalNotExpression'):
            continue
          # Fix for Issue 36, inside expressions
          # do not have left/right
          if (lv_cnst_i.expr.kind.name == 'InsideExpression'):
            continue
          # Fix for Issue 37, dist expressions
          # do not have left/right
          if (lv_cnst_i.expr.kind.name == 'ExpressionOrDist'):
            FUNC_CNST_DIST_COL_EQ (lv_cnst_i)
            continue
          if (lv_cnst_i.expr.left.kind.name == 'InvocationExpression'):
            lv_cnst_expr_s = lv_cnst_i.expr.left.__str__()
            lv_arr_red_methods = [".sum()", ".sum ()",
                    ".product()", ".product ()", 
                    ".and()", ".and ()",
                    ".or()", ".or ()",
                    ".xor()", ".xor ()"]
            if any([x in lv_cnst_expr_s for x in lv_arr_red_methods]):
              msg  = 'Potentially incorrect constraint expression!'
              msg += ' An expression involving the array-reduction methods'
              msg += ' sum()/product()/and()/or()/xor()'
              msg += ' was found, but is missing an explicit cast.'
              msg += ' This can lead to strange results as'
              msg += ' array reduction methods return an expression'
              msg += ' of the size of'
              msg += ' its elements, check if you need a with'
              msg += ' (int\'( cast around the following expression:'
              msg += lv_cnst_expr_s
              lv_rule_id = "FUNC_CNST_MISSING_CAST"
              pyslint_msg(lv_rule_id, msg)

def FUNC_CNST_WRONG_OPER_PRI (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):
      if (cl_item.kind.name == 'ConstraintDeclaration'):
        for lv_cnst_i in (cl_item.block.items):
          if (not hasattr(lv_cnst_i, 'expr')):
            continue
          if (not hasattr(lv_cnst_i.expr, 'operatorToken')):
            continue

          if (lv_cnst_i.expr.operatorToken.kind.name == 'DoubleAnd' or
              lv_cnst_i.expr.operatorToken.kind.name == 'DoubleOr'
             ):
            lv_cnst_expr_s = lv_cnst_i.expr.__str__()
            if (
                lv_cnst_i.expr.left.operatorToken.kind.name == 'DoubleEquals' or
                lv_cnst_i.expr.left.operatorToken.kind.name == 'ExclamationEquals'
                ):
              msg  = 'Potentially incorrect constraint expression!'
              msg += ' An expression involving operators with different'
              msg += ' precedence is observed. As per LRM, Equality'
              msg += ' operators have higher precedence than Logical operators'
              msg += ' Review and use \'( )\' appropriately'
              msg += ' around the constraint expression'
              msg += lv_cnst_expr_s
              lv_rule_id = "FUNC_CNST_WRONG_OPER_PRI"
              pyslint_msg(lv_rule_id, msg)

def COMPAT_CG_OPT_PI_CL(lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_item_i in (lv_m.items):
      if (cl_item_i.kind.name == 'CovergroupDeclaration'):
        for lv_cg_m_i in cl_item_i.members:
          if (lv_cg_m_i.kind.name == 'CoverageOption'):
            lv_cg_name = cl_item_i.name.valueText
            lv_cg_opt = lv_cg_m_i.expr.left.__str__()
            if ('type_option.per_instance' in lv_cg_opt):
              msg = 'Found \'type_option.per_instance\' '
              msg += 'inside a covergroup: '
              msg += lv_cg_name
              msg += '\nIEEE 1800 LRM does not'
              msg += ' allow such usage though some tools do compile. \n'
              msg += 'To avoid compatibility issues,'
              msg += ' please move the per_instance to'
              msg += ' \'option.per_instance \''
              lv_rule_id = "COMPAT_CG_OPT_PI_CL"
              pyslint_msg(lv_rule_id, msg)

def REUSE_CG_NO_ILBINS_CL(lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_item_i in (lv_m.items):
      if (cl_item_i.kind.name == 'CovergroupDeclaration'):
        lv_cg_name = cl_item_i.name.valueText.strip()
        for lv_cg_m_i in cl_item_i.members:
          if (lv_cg_m_i.kind.name == 'Coverpoint'):
            lv_cpt_expr = lv_cg_m_i.expr.__str__()
            lv_cpt_label = lv_cg_m_i.label.__str__()
            lv_cpt_name = lv_cpt_label + lv_cpt_expr
            lv_cpt_name = lv_cpt_name.strip()
            for lv_cpt_m_i in lv_cg_m_i.members:
              if (lv_cpt_m_i.kind.name == 'CoverageBins'):
                lv_cpt_bin_s = lv_cpt_m_i.keyword.__str__()
                if ('illegal_bins' in lv_cpt_bin_s):
                  lv_cpt_bin_name = lv_cpt_m_i.name.valueText
                  msg = 'Found \'illegal_bins\' under user-defined bins: \n'
                  msg += 'covergroup: '
                  msg += lv_cg_name
                  msg += ' for coverpoint: '
                  msg += lv_cpt_name + ' '
                  msg += lv_cpt_bin_name
                  msg += '\nWhile IEEE 1800 LRM allows this syntax, this '
                  msg += 'is bad for REUSE aspect as it does not flag '
                  msg += 'as UVM_ERROR or $error. \n'
                  msg += 'Also if coverage is turned OFF, this error '
                  msg += 'is likely to go unflagged. '
                  msg += 'Recommended to use \'ignore_bins\' instead \n'
                  msg += 'from coverage perspective and add SVA or '
                  msg += 'scoreboard for illegal values.'
                  lv_rule_id = "REUSE_CG_NO_ILBINS_CL"
                  pyslint_msg(lv_rule_id, msg)

def REUSE_NO_WILDC_AA_CL(lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_item_i in (lv_m.items):
      if (cl_item_i.kind.name == 'ClassPropertyDeclaration'):
        lv_decl_str_s = cl_item_i.__str__()
        for lv_decl_i in cl_item_i.declaration.declarators:
          if (not hasattr(lv_decl_i, 'dimensions')):
            continue
          for lv_decl_dim_i in lv_decl_i.dimensions:
            if (lv_decl_dim_i.specifier.kind.name == 'WildcardDimensionSpecifier'):
              msg = 'Found an associative array declaration with wild-card as key\n'
              msg += lv_decl_str_s
              msg += '\nThis is bad for reuse as it does not allow \'foreach\' iterator and other handy built-in functions.\n'
              msg += 'Consider using a typed key such as int/string etc.'
              lv_rule_id = 'REUSE_NO_WILDC_AA_CL'
              pyslint_msg(lv_rule_id, msg)

def PERF_CG_NO_ABIN_W_DEF_CL(lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_item_i in (lv_m.items):
      if (cl_item_i.kind.name == 'CovergroupDeclaration'):
        lv_cg_name =  cl_item_i.name.valueText.strip()
        for lv_cg_m_i in cl_item_i.members:
          if (lv_cg_m_i.kind.name == 'Coverpoint'):
            lv_cpt_expr = lv_cg_m_i.expr.__str__()
            lv_cpt_label = lv_cg_m_i.label.__str__()
            if (lv_cpt_label == 'None'):
              lv_cpt_label = ''
            lv_cpt_name = lv_cpt_label + lv_cpt_expr
            lv_cpt_name = lv_cpt_name.strip()
            for lv_cpt_m_i in lv_cg_m_i.members:
              if (lv_cpt_m_i.size is None):
                continue
              if (lv_cpt_m_i.size.kind.name == 'CoverageBinsArraySize'):
                if (lv_cpt_m_i.size.expr is None):
                  lv_arr_bin_rhs_s = lv_cpt_m_i.initializer.__str__().strip()
                  if (lv_arr_bin_rhs_s == 'default'):
                    lv_cpt_bin_name = lv_cpt_m_i.name.valueText
                    msg = 'Found Array-bins: \n'
                    msg += '\tcovergroup: '
                    msg += lv_cg_name
                    msg += '\n\tcoverpoint: '
                    msg += lv_cpt_name + '\n\tBIN: '
                    msg += lv_cpt_bin_name + '\n\t'
                    msg += lv_cpt_m_i.__str__().strip()
                    msg += '\n\n\tWhile IEEE 1800 LRM allows this syntax, this '
                    msg += 'is bad for Performance aspect as it ends up creating'
                    msg += ' large number of bins. Recommended to remove this bin.'
                    lv_rule_id = 'PERF_CG_NO_ABIN_W_DEF_CL'
                    pyslint_msg(lv_rule_id, msg)

def NAME_CG_PREFIX(lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_item_i in (lv_m.items):
      if (cl_item_i.kind.name == 'CovergroupDeclaration'):
        lv_cg_name =  cl_item_i.name.valueText
        lv_exp_s = 'cg_'
        if (not lv_cg_name.startswith(lv_exp_s)):
          msg = 'Improper naming of identifier: ' 
          msg += lv_cg_name
          msg += ': expected prefix: '
          msg += lv_exp_s
          lv_rule_id = "NAME_CG_PREFIX"
          pyslint_msg(lv_rule_id, msg)

  if (lv_m.kind.name == 'CovergroupDeclaration'):
    lv_cg_name =  lv_m.name.valueText
    lv_exp_s = 'cg_'
    if (not lv_cg_name.startswith(lv_exp_s)):
      msg = 'Improper naming of identifier: ' 
      msg += lv_cg_name
      msg += ': expected prefix: '
      msg += lv_exp_s
      lv_rule_id = 'NAME_CG_PREFIX'
      pyslint_msg(lv_rule_id, msg)

def DBG_SVA_AST_MISSING_LABEL(lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    lv_sva_vdir = lv_m.statement.keyword.valueText
    if (lv_sva_vdir != 'assert'):
      return
    if (lv_m.statement.label is None):
      msg = 'Unnamed assertion - use a meaningful label: ' 
      msg += str(lv_m.statement)
      lv_rule_id = 'DBG_SVA_AST_MISSING_LABEL'
      pyslint_msg (lv_rule_id, msg)

def NAME_AST_PREFIX (lv_m):

  if (lv_m.kind.name == 'ConcurrentAssertionMember'):

    lv_sva_vdir = lv_m.statement.keyword.valueText
    if (lv_sva_vdir != 'assert'):
      return

    if (lv_m.statement.label is None):
      return

    lv_label = lv_m.statement.label.name.value

    lv_exp_s = sv_prefix_d['assert']
    if (not lv_label.startswith(lv_exp_s)):
      msg = 'Improper naming of assert directive: ' 
      msg += lv_label
      msg += ': expected prefix: '
      msg += lv_exp_s
      lv_rule_id = 'NAME_AST_PREFIX'
      pyslint_msg (lv_rule_id, msg)


def NAME_ASM_PREFIX(lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      msg = 'Unnamed assumption - use a meaningful label: ' 
      msg += str(lv_m.statement)
      lv_rule_id = "DBG_SVA_MISSING_LABEL"
      pyslint_msg(lv_rule_id, msg)
    else:
      lv_label = lv_m.statement.label.name.value
      lv_sva_vdir = lv_m.statement.keyword.valueText
      if (lv_sva_vdir != 'assume'):
        return

      lv_exp_s = sv_prefix_d['assume']
      if (not lv_label.startswith(lv_exp_s)):
        msg = 'Improper naming of assume directive: ' 
        msg += lv_label
        msg += ': expected prefix: '
        msg += lv_exp_s
        lv_rule_id = 'NAME_ASM_PREFIX'
        pyslint_msg(lv_rule_id, msg)

def NAME_COV_PREFIX(lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      msg = 'Unnamed assumption - use a meaningful label: ' 
      msg += str(lv_m.statement)
      lv_rule_id = "DBG_SVA_MISSING_LABEL"
      pyslint_msg(lv_rule_id, msg)
    else:
      lv_label = lv_m.statement.label.name.value
      lv_sva_vdir = lv_m.statement.keyword.valueText
      if (lv_sva_vdir != 'cover'):
        return

      lv_exp_s = sv_prefix_d['cover']
      if (not lv_label.startswith(lv_exp_s)):
        msg = 'Improper naming of cover directive: ' 
        msg += lv_label
        msg += ': expected prefix: '
        msg += lv_exp_s
        lv_rule_id = 'NAME_COV_PREFIX'
        pyslint_msg(lv_rule_id, msg)


def COMPAT_SVA_NO_DEGEN_AST (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):

    lv_found_rep_val = False

    lv_p_expr = lv_m.statement.propertySpec
    lv_p_str = lv_p_expr.__str__()

    if (hasattr(lv_p_expr, 'expr')):
      lv_p_expr_r = lv_p_expr.expr

      if (hasattr(lv_p_expr_r, 'right') and
          hasattr(lv_p_expr_r.right, 'expr')):
        lv_p_expr_r_1 = lv_p_expr_r.right.expr

      if (hasattr(lv_p_expr_r, 'left')):
        lv_p_expr_r_1 = lv_p_expr_r.left.expr
        #TBD move the below code to a new def
        # and make it common for both ANT and CNSQ


        if (hasattr(lv_p_expr_r_1, 'first')):
          lv_p_expr_r_1 = lv_p_expr_r_1.first

        if (hasattr(lv_p_expr_r_1, 'repetition')):
          lv_p_expr_r_2 = lv_p_expr_r_1.repetition

          if (hasattr(lv_p_expr_r_2, 'selector')):
            lv_p_expr_r_3 = lv_p_expr_r_2.selector

            if (hasattr(lv_p_expr_r_3, 'expr')):
              lv_p_expr_r_4 = lv_p_expr_r_3.expr
              lv_rep_val = "UNKNOWN"
              lv_rep_val = lv_p_expr_r_4.literal.valueText.strip()
              lv_found_rep_val = True

            if (hasattr(lv_p_expr_r_3, 'left')):
              lv_p_expr_r_4 = lv_p_expr_r_3.left
              lv_rep_val = "UNKNOWN"
              lv_rep_val = lv_p_expr_r_4.literal.valueText.strip()
              lv_found_rep_val = True

      if (hasattr(lv_m, 'propertySpec') and
          hasattr(lv_p_expr_r, 'expr')):
        lv_p_expr_r = lv_m.propertySpec.expr.expr.expr
        if (hasattr(lv_p_expr_r, 'repetition')):
          lv_rep_val = lv_m.propertySpec.expr.expr.expr.repetition.selector.expr.literal.valueText.strip()
          lv_found_rep_val = True


    if (hasattr(lv_p_expr, 'right')):
      lv_p_expr_r = lv_m.propertySpec.expr.right.expr
      if (hasattr(lv_p_expr_r, 'repetition')):
        lv_p_expr_r = lv_m.propertySpec.expr.right.expr.repetition
        if (hasattr(lv_p_expr_r, 'selector')):
          lv_rep_val = lv_m.propertySpec.expr.right.expr.repetition.selector.expr.literal.valueText.strip()
          lv_found_rep_val = True

    if (lv_found_rep_val and lv_rep_val == "0"):
      msg = 'Empty match ([*0] or variants) found in a property expression. \n'
      msg += '\tThough some compilers allow this, IEEE 1800 LRM prevents'
      msg += ' such usage, so for maximum compatibility across EDA \n'
      msg += '\ttools and LRM compliance, please remove the empty match. \n'
      msg += lv_p_str
      lu_rule_id = 'COMPAT_SVA_NO_DEGEN_AST'
      pyslint_msg (lu_rule_id, msg)

def COMPAT_SVA_NO_S_UNTIL_WITH (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):

    lv_found_rep_val = False

    lv_p_expr = lv_m.statement.propertySpec
    lv_p_str = lv_p_expr.__str__()

    if (hasattr(lv_p_expr, 'expr')):
      lv_p_expr_r = lv_p_expr.expr

      if (hasattr(lv_p_expr_r, 'right') and
          hasattr(lv_p_expr_r.right, 'op')):
        lv_p_expr_r_1 = lv_p_expr_r.right.op

        if (lv_p_expr_r_1.kind.name == 'SUntilWithKeyword'):

          msg = 'Found usage of s_util_with on consequent of a concurrent assertion. \n'
          msg += '\tThough LRM supports this, some compilers do NOT support this.'
          msg += ' So for maximum compatibility across EDA \n'
          msg += '\ttools consider remodeling this SVA. \n'
          msg += lv_p_str
          lu_rule_id = 'COMPAT_SVA_NO_S_UNTIL_WITH'
          pyslint_msg (lu_rule_id, msg)


def COMPAT_SVA_PROP_MISSING_SEMI(lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration'):
    lv_code_s = str(lv_m)
    if (';' not in str(lv_m.optionalSemi)):
      msg = 'A Concurrent property definition was found without \n'
      msg += '\t semicolon at the end \';\' Though some'
      msg += ' compilers allow this, others do not.'
      msg += ' So for maximum \n'
      msg += '\t compatibility across EDA tools,'
      msg += ' please add \';\' at the end.\n'
      msg += lv_code_s
      lv_rule_id = 'COMPAT_SVA_PROP_MISSING_SEMI'
      pyslint_msg(lv_rule_id, msg)

def COMPAT_SVA_NO_DEGEN_CONSEQ(lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration' or
      lv_m.kind.name == 'ConcurrentAssertionMember'):

    if (lv_m.kind.name == 'ConcurrentAssertionMember'):
      lv_p_expr = lv_m.statement.propertySpec.expr
    else:
      lv_p_expr = lv_m.propertySpec.expr

    lv_p_str = lv_p_expr.__str__()
    lv_found_rep_val = False

    if (hasattr(lv_p_expr, 'expr')):
      lv_p_expr_r = lv_p_expr.expr
      if (hasattr(lv_p_expr_r, 'right')):
        lv_p_expr_r_1 = lv_p_expr_r.right.expr
        if (hasattr(lv_p_expr_r_1, 'repetition')):
          lv_p_expr_r_2 = lv_p_expr_r_1.repetition
          if (hasattr(lv_p_expr_r_2, 'selector')):
            lv_p_expr_r_3 = lv_p_expr_r_2.selector
            if (hasattr(lv_p_expr_r_3, 'left')):
              lv_p_expr_r_4 = lv_p_expr_r_3.left
              lv_rep_val = "UNKNOWN"
              lv_rep_val = lv_p_expr_r_4.literal.valueText.strip()
              lv_found_rep_val = True

      if (hasattr(lv_p_expr_r, 'expr')):
        lv_p_expr_r = lv_p_expr_r.expr
        if (hasattr(lv_p_expr_r, 'repetition')):
          if (lv_p_expr_r.repetition is not None):
            lv_p_expr_r = lv_p_expr_r.repetition
            if (hasattr(lv_p_expr_r, 'selector')):
              lv_rep_val = lv_p_expr_r.selector.expr.literal.valueText.strip()
              lv_found_rep_val = True


    if (hasattr(lv_p_expr, 'right')):
      if (hasattr(lv_p_expr.right, 'expr')):
        lv_p_expr_r = lv_p_expr.right.expr
        if (hasattr(lv_p_expr_r, 'first')):
          lv_p_expr_r =  lv_p_expr_r.first
        if (hasattr(lv_p_expr_r, 'repetition')):
          lv_p_expr_r = lv_p_expr_r.repetition
          if (hasattr(lv_p_expr_r, 'selector')):
            lv_p_expr_r = lv_p_expr_r.selector
            if (hasattr(lv_p_expr_r, 'expr')):
              lv_rep_val = lv_p_expr_r.expr.literal.valueText.strip()
              lv_found_rep_val = True

    if (lv_found_rep_val and lv_rep_val == "0"):
      msg = 'Empty match ([*0] or variants) found in a property expression. \n'
      msg += '\tThough some compilers allow this, IEEE 1800 LRM prevents'
      msg += ' such usage, so for maximum compatibility across EDA \n'
      msg += '\ttools and LRM compliance, please remove the empty match. \n'
      msg += lv_p_str
      lv_rule_id = 'COMPAT_SVA_NO_DEGEN_CONSEQ'
      pyslint_msg(lv_rule_id, msg)

def NAME_PROP_PREFIX(lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration'):
    lv_prop_label = lv_m.name.valueText
    lv_exp_s = sv_prefix_d['prop']
    if (not lv_prop_label.startswith(lv_exp_s)):
      msg = 'Improper naming of property: ' 
      msg += lv_prop_label
      msg += ': expected prefix: '
      msg += lv_exp_s
      lv_rule_id = 'NAME_PROP_PREFIX'
      pyslint_msg(lv_rule_id, msg)

def DBG_SVA_MISSING_ENDLABEL(lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration'):
    if (lv_m.endBlockName is None):
      lv_prop_label = lv_m.name.valueText
      msg = 'Missing End Label for property: ' 
      msg += lv_prop_label
      lv_rule_id = 'DBG_SVA_MISSING_ENDLABEL'
      pyslint_msg(lv_rule_id, msg)

def DBG_CL_MISSING_ENDLABEL(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    if (lv_cu_scope.endBlockName is None):
      lv_cl_label = lv_cu_scope.name.valueText
      msg = 'Missing End Label for class: ' 
      msg += lv_cl_label
      lv_rule_id = 'DBG_CL_MISSING_ENDLABEL'
      pyslint_msg(lv_rule_id, msg)

def PERF_SVA_NO_PASS_AB(lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.action.statement is None):
      return
    if (lv_m.statement.action.statement.kind.name == 'EmptyStatement'):
      return

    if (lv_m.statement.action.statement is not None):
      msg = 'Avoid using PASS Action block - likely to cause too many vacuous prints: ' 
      msg += str(lv_m.statement)
      lv_rule_id = 'PERF_SVA_NO_PASS_AB'
      pyslint_msg(lv_rule_id, msg)

def FUNC_SVA_MISSING_FAIL_AB(lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      return

    lv_label = lv_m.statement.label.name.value
    lv_sva_vdir = lv_m.statement.keyword.valueText

    if (lv_sva_vdir != 'assert'):
      return

    if (lv_m.statement.action.elseClause is None):
      msg = 'Missing FAIL Action block - use $error/`uvm_error: ' 
      msg += str(lv_m.statement)
      lv_rule_id = 'FUNC_SVA_MISSING_FAIL_AB'
      pyslint_msg(lv_rule_id, msg)

def pyslint_argparse():
  # Create the parser
  parser = argparse.ArgumentParser()
  # Add an argument
  parser.add_argument('-t', '--test', type=str, required=True)
  # Parse the argument
  args = parser.parse_args()
  return args

def pyslint_update_prefixes():
  lv_sv_prefix_d = {}
  lv_sv_prefix_d.update({"prop": "p_"})
  lv_sv_prefix_d.update({"cover": "c_"})
  lv_sv_prefix_d.update({"assert": "a_"})
  lv_sv_prefix_d.update({"assume": "m_"})
  return lv_sv_prefix_d

def pyslint_update_suffixes():
  lv_sv_suffix_d = {}
  lv_sv_suffix_d.update({"intf": "_if"})
  lv_sv_suffix_d.update({"class": "_c"})
  lv_sv_suffix_d.update({"cnst": "_cst"})
  lv_sv_suffix_d.update({"mod": "_m"})
  return lv_sv_suffix_d

def chk_name_style_prefix(lv_rule_id, lv_name, lv_exp_p):
  if (lv_name.startswith(lv_exp_p)):
    if (print_verbose):
      print('AF: Good naming: ', lv_name)
  else:
    msg = 'Improper naming of identifier: ' 
    msg += lv_name
    msg += ': expected prefix: '
    msg += lv_exp_p
    pyslint_msg(lv_rule_id, msg)

def chk_name_style_suffix(lv_rule_id, lv_name, lv_exp_s):
  if (lv_name.endswith(lv_exp_s)): 
    if (print_verbose):
      print('AF: Good naming: ', lv_name)
  else:
    msg = 'Improper naming of identifier: ' 
    msg += lv_name
    msg += ': expected suffix: '
    msg += lv_exp_s
    pyslint_msg(lv_rule_id, msg)

def FUNC_NO_2STATE_IN_INTF(lv_intf_scope):
  for lv_intf_mem_i in lv_intf_scope.members:
    if (lv_intf_mem_i.kind.name == 'DataDeclaration'):
      if (lv_intf_mem_i.type.kind.name == 'BitType'):
        lv_var_decl = lv_intf_mem_i.declarators.getFirstToken()
        lv_name = lv_var_decl.valueText
        msg = 'Potential DUT bug hiding construct in use: '
        msg += ' Inside SystemVerilog interface, it is recommended'
        msg += ' to use only 4-state signals/nets.'
        msg += ' Found a 2-state declaration as: '
        msg += lv_intf_mem_i.__str__()
        lv_rule_id = 'FUNC_NO_2STATE_IN_INTF'
        pyslint_msg(lv_rule_id, msg)

af_dpi_method_l = list()

def af_dpi_collect_info(lv_dpi_m):
  lv_dpi_d = {}
  lv_dpi_d['name'] = lv_dpi_m.name.__str__().strip()
  lv_dpi_d['type'] = lv_dpi_m.functionOrTask.__str__().strip()
  af_dpi_method_l.append(lv_dpi_d.copy())

def FUNC_DPI_FN_MISSING_RTYPE(lv_dpi_m):
  if (not hasattr(lv_dpi_m, 'method')):
    return

  if (str(lv_dpi_m.method.keyword).strip() == 'task'):
    return

  lv_code_s = lv_dpi_m.__str__()
  if (lv_dpi_m.method.returnType.kind.name == 'ImplicitType'):
    msg = 'DPI import functions should specify \n'
    msg += '\t return type as per LRM.'
    msg += ' Using Implicit return type (of logic) can lead to \n'
    msg += '\t functional issues leading to unexpected results. Please specify'
    msg += ' return type as void/bit etc. \n'
    msg += '\t Preferably use 2-state type. \n'
    msg += lv_code_s
    lv_rule_id = 'FUNC_DPI_FN_MISSING_RTYPE'
    pyslint_msg(lv_rule_id, msg)

def COMPAT_DPI_NO_PURE_TASK(lv_dpi_m):
  '''
  Add this once PySlang supports this
  lv_rval_type_s = lv_dpi_mem.method.returnType.keyword.__str__().strip()
  lv_rval_4st_types = ["integer", "logic",
                    "reg"]
  if any([x in lv_rval_type_s for x in lv_rval_4st_types]):
    msg = 'DPI functions shall use 2-state types in return value.'
    msg += ' Using 4-state type can lead to unnecessary complication'
    msg += ' as C-side does not naturally support 4-state value system'
    msg += ' Found code as: \n'
    msg += str(lv_dpi_mem)
    lv_rule_id = 'COMPAT_DPI_NO_PURE_TASK'
    pyslint_msg(lv_rule_id, msg)
  '''

def FUNC_DPI_NO_4STATE_IN_RETURN(lv_dpi_mem):
  if (not hasattr(lv_dpi_mem, 'method')):
    return
  if (not hasattr(lv_dpi_mem.method.returnType, 'keyword')):
    return

  lv_rval_type_s = lv_dpi_mem.method.returnType.keyword.__str__().strip()
  lv_rval_4st_types = ["integer", "logic",
                    "reg"]
  if any([x in lv_rval_type_s for x in lv_rval_4st_types]):
    msg = 'DPI functions shall use 2-state types in return value.'
    msg += ' Using 4-state type can lead to unnecessary complication'
    msg += ' as C-side does not naturally support 4-state value system'
    msg += ' Found code as: \n'
    msg += str(lv_dpi_mem)
    lv_rule_id = 'FUNC_DPI_NO_4STATE_IN_RETURN'
    pyslint_msg(lv_rule_id, msg)


def FUNC_DPI_NO_4STATE_IN_ARGS(lv_dpi_mem):
  if(not hasattr(lv_dpi_mem, 'method')):
    return
  if (lv_dpi_mem.method.portList is None):
    return
  for lv_dpi_args_i in lv_dpi_mem.method.portList:
    if (lv_dpi_args_i.kind.name == 'SeparatedList'):
      for lv_dpi_ports_i in lv_dpi_args_i:
        if (lv_dpi_ports_i.kind.name != 'Comma'):
          lv_rval_type_s = lv_dpi_ports_i.dataType.__str__().strip()
          lv_rval_4st_types = ["integer", "logic",
                    "reg", "None"]
          if any([x in lv_rval_type_s for x in lv_rval_4st_types]):
            msg = 'DPI functions shall use arguments of 2-state types.\n'
            msg += '\t Using 4-state type can lead to unnecessary complications\n'
            msg += '\t as C-side does not naturally support 4-state value system'
            msg += str(lv_dpi_mem)
            lv_rule_id = 'FUNC_DPI_NO_4STATE_IN_ARGS'
            pyslint_msg(lv_rule_id, msg)



def COMPAT_DPI_NO_MDA(lv_dpi_mem):
  if(not hasattr(lv_dpi_mem, 'method')):
    return
  if (lv_dpi_mem.method.portList is None):
    return

  for lv_dpi_args_i in lv_dpi_mem.method.portList:
    if (lv_dpi_args_i.kind.name == 'SeparatedList'):
      for lv_dpi_ports_i in lv_dpi_args_i:
        if (lv_dpi_ports_i.kind.name != 'Comma'):
          lv_dpi_arg_dim_s = lv_dpi_ports_i.declarator.dimensions.__str__().strip()
          if (op.countOf(lv_dpi_arg_dim_s, "[") > 1):
            msg = 'DPI method with Multi-Dimensional Array as arguments'
            msg += ' was found. \n\tWhile LRM allows this, some tools do not'
            msg += ' fully support. To avoid compatibility issues, \n'
            msg += '\tplease remodel the code:'
            msg += str(lv_dpi_mem)
            lv_rule_id = 'COMPAT_DPI_NO_MDA'
            pyslint_msg(lv_rule_id, msg)



def COMPAT_DPI_OLD_SPECSTR(lv_dpi_mem):
  lv_spec_str_val_s = lv_dpi_mem.specString.__str__().strip()
  if (lv_spec_str_val_s != '\"DPI-C\"'):
    msg = 'Wrong Spec-STR in DPI declaration'
    msg += ' IEEE 1800-2012 specifies \"DPI-C\" as Spec-STR.'
    msg += ' Found code as: \n'
    msg += str(lv_dpi_mem)
    lv_rule_id = 'COMPAT_DPI_OLD_SPECSTR'
    pyslint_msg(lv_rule_id, msg)

def COMPAT_SVA_NO_CONC_IN_FE(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'InitialBlock'):
        if (not hasattr(lv_mod_mem_i.statement, 'items')):
          continue
        for lv_init_items_i in lv_mod_mem_i.statement.items:

          if (lv_init_items_i.kind.name == 'ForeverStatement'):
            if (not hasattr(lv_init_items_i.statement.statement, 'items')):
              continue
            for lv_fe_i in lv_init_items_i.statement.statement.items:
              lv_code_s = lv_fe_i.__str__()
              if (lv_fe_i.kind.name == 'AssertPropertyStatement'):
                msg = 'A procedural concurrent assertion was found'
                msg += ' inside a forever loop; IEEE 1800 LRM does not'
                msg += ' allow such usage though some tools do compile'
                msg += ' To avoid compatibility issues,'
                msg += ' please remodel the code:'
                msg += str(lv_code_s)
                lv_rule_id = 'COMPAT_SVA_NO_CONC_IN_FE'
                pyslint_msg(lv_rule_id, msg)

def FUNC_NO_BEGIN_IN_TIMING_CTRL(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'TaskDeclaration'):
        lv_task_name = str(lv_mod_mem_i.prototype)
        for lv_task_items_i in lv_mod_mem_i.items:
          if (lv_task_items_i.kind.name == 'TimingControlStatement'):
            lv_tmp_s = str(lv_task_items_i)
            lv_tmp_s_l = lv_tmp_s.splitlines()
            lv_code_s = ''.join(lv_tmp_s_l[:3])

            if ((lv_task_items_i.statement.kind.name == 'SequentialBlockStatement')):
              msg = 'A task with TimingControl like @(posedge clk) was\n'
              msg += '\t found along with a \'begin..end\'\n'
              msg += '\t This is likely a typo-error and may lead to'
              msg += ' unexpected behaviour of the BFM code. \n'
              msg += '\t Task where this was found:'
              msg += lv_task_name + '\n'
              msg += '\t Relevant code snippet: \n'
              msg += lv_code_s
              lv_rule_id = 'FUNC_NO_BEGIN_IN_TIMING_CTRL'
              pyslint_msg(lv_rule_id, msg)



def DBG_AVOID_BEGIN_IN_TASK(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'TaskDeclaration'):
        for lv_task_items_i in lv_mod_mem_i.items:
          if (lv_task_items_i.kind.name == 'SequentialBlockStatement'):
            lv_code_s = str(lv_mod_mem_i.prototype)
            msg = 'A task with begin..end was found.\n'
            msg += '\t This is likely a legacy Verilog coding syle as SystemVerilog \n'
            msg += '\t makes this optional and it is recommended'
            msg += ' coding style to avoid begin..end \n'
            msg += '\t inside task to improve readability and'
            msg += ' maintainability of codebase.\n'
            msg += '\t Please remove the redundant begin..end \n'
            msg += lv_code_s
            lv_rule_id = 'DBG_AVOID_BEGIN_IN_TASK'
            pyslint_msg(lv_rule_id, msg)

# https://verificationacademy.com/forums/systemverilog/function-arguments-not-initializing-variable-inside-body#reply-54684
def FUNC_NO_INIT_OF_STATIC_VAR_IN_SFN(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'FunctionDeclaration'):
        lv_fn_name = str(lv_mod_mem_i.prototype.name)
        if (str(lv_mod_mem_i.prototype.lifetime).strip() == 'automatic'):
          lv_fn_is_auto = True
          continue

        for lv_fn_items_i in lv_mod_mem_i.items:
          if (lv_fn_items_i.kind.name == 'DataDeclaration'):
            lv_var_lt_static = True


            lv_var_lifetime = str(lv_fn_items_i.modifiers).strip()
            if (lv_var_lifetime == 'automatic'):
              lv_var_lt_static = False

            for lv_decl_i in lv_fn_items_i.declarators:
              if ((lv_decl_i.initializer is not None) and
                  (lv_var_lt_static)):
                lv_code_s = str(lv_fn_items_i)
                msg = 'A static function has a variable declaration \n'
                msg += '\t with initialization. In most cases this code will'
                msg += ' likely behave unexpected manner functionally.\n'
                msg += ' \t This is due to the fact that'
                msg += ' initialization of static variables happens'
                msg += ' before time 0,\n'
                msg += '\t not when calling the function.'
                msg += '\t Please remove the initialization\n'
                msg += lv_code_s
                lv_rule_id = 'FUNC_NO_INIT_OF_STATIC_VAR_IN_SFN'
                pyslint_msg(lv_rule_id, msg)

# https://verificationacademy.com/forums/systemverilog/function-arguments-not-initializing-variable-inside-body#reply-54684
def COMPAT_VAR_DINIT_IN_SFN(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'FunctionDeclaration'):
        lv_fn_name = str(lv_mod_mem_i.prototype.name)
        if (str(lv_mod_mem_i.prototype.lifetime).strip() == 'automatic'):
          lv_fn_is_auto = True
          continue

        for lv_fn_items_i in lv_mod_mem_i.items:
          if (lv_fn_items_i.kind.name == 'DataDeclaration'):
            lv_var_lt_def = True


            lv_var_lifetime = str(lv_fn_items_i.modifiers).strip()
            if ((lv_var_lifetime == 'automatic') or
                (lv_var_lifetime == 'static')):
              lv_var_lt_def = False

            for lv_decl_i in lv_fn_items_i.declarators:
              if ((lv_decl_i.initializer is not None) and
                  (lv_var_lt_def)):
                lv_code_s = str(lv_fn_items_i)
                msg = 'A static function has a variable declaration \n'
                msg += '\t with initialization. LRM 1800 mandates that'
                msg += ' lifetime of such variables be specified \n'
                msg += '\t explicitly and not use the default' 
                msg += ' lifetime (static).\n'
                msg += '\t Though some tools do compile this code,'
                msg += ' others do NOT (and LRM compliant). \n'
                msg += '\t To maximize compatibility across tools,'
                msg += ' Please remove the initialization\n'
                msg += '\t or add an explicit lifetime for this variable.'
                msg += lv_code_s
                lv_rule_id = 'COMPAT_VAR_DINIT_IN_SFN'
                pyslint_msg(lv_rule_id, msg)

def DBG_AVOID_BEGIN_IN_FN(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'FunctionDeclaration'):
        for lv_fn_items_i in lv_mod_mem_i.items:
          if (lv_fn_items_i.kind.name == 'SequentialBlockStatement'):
            lv_code_s = str(lv_mod_mem_i.prototype)
            msg = 'A function with begin..end was found.\n'
            msg += '\t This is likely a legacy Verilog coding syle as SystemVerilog \n'
            msg += '\t makes this optional and it is recommended'
            msg += ' coding style to avoid begin..end \n'
            msg += '\t inside function to improve readability and'
            msg += ' maintainability of codebase.\n'
            msg += '\t Please remove the redundant begin..end \n'
            msg += lv_code_s
            lv_rule_id = 'DBG_AVOID_BEGIN_IN_FN'
            pyslint_msg(lv_rule_id, msg)

def COMPAT_NO_REF_IN_STATIC_FN(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'FunctionDeclaration'):
        lv_found_ref_arg = False
        lv_code_s = str(lv_mod_mem_i.prototype)
        if (not hasattr(lv_mod_mem_i.prototype.portList, 'ports')):
          continue
        for lv_fn_p_i in lv_mod_mem_i.prototype.portList.ports:
          if (lv_fn_p_i.kind.name == 'FunctionPort'):
            if (str(lv_fn_p_i.direction).strip() == 'ref'):
              lv_found_ref_arg = True
              break
        if (lv_found_ref_arg and
            str(lv_mod_mem_i.prototype.lifetime).strip() != 'automatic'):

          msg = 'A function with \'ref\' argument was found. \n'
          msg += '\t IEEE 1800 LRM requires such functions to be'
          msg += ' declared automatic. Some tools do not check \n'
          msg += '\t this rule strictly leading to incompatible code.'
          msg += ' Add keyword \'automatic\' before the \n\t function'
          msg += ' name or remove the \'ref\' qualifier to the argument.'
          msg += lv_code_s
          lv_rule_id = 'COMPAT_NO_REF_IN_STATIC_FN'
          pyslint_msg(lv_rule_id, msg)


        for lv_fn_items_i in lv_mod_mem_i.items:
          if (lv_fn_items_i.kind.name == 'SequentialBlockStatement'):
            lv_code_s = str(lv_mod_mem_i.prototype)

def COMPAT_SVA_NO_EXPECT_EXPR_IN_INIT(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'InitialBlock'):
        if (not hasattr(lv_mod_mem_i.statement, 'items')):
          continue
        for lv_init_items_i in lv_mod_mem_i.statement.items:
          if (lv_init_items_i.kind.name == 'ExpectPropertyStatement'):
            if (
                hasattr(lv_init_items_i, 'propertySpec') and
                hasattr(lv_init_items_i.propertySpec, 'expr') and
                hasattr(lv_init_items_i.propertySpec.expr, 'expr') and
                hasattr(lv_init_items_i.propertySpec.expr.expr, 'elements')
              ):
              lv_code_s = lv_init_items_i.__str__()
              msg = 'A procedural \'expect\' construct with temporal'
              msg += ' expression was found'
              msg += ' inside an initial block; IEEE 1800 LRM does '
              msg += ' allow such usage though some tools do NOT support'
              msg += ' To avoid compatibility issues,'
              msg += ' please remodel the code:'
              msg += str(lv_code_s)
              lv_rule_id = 'COMPAT_SVA_NO_EXPECT_EXPR_IN_INIT'
              pyslint_msg(lv_rule_id, msg)

            '''
            if (not hasattr(lv_init_items_i.statement.statement, 'items')):
              continue
            for lv_fe_i in lv_init_items_i.statement.statement.items:
              lv_code_s = lv_fe_i.__str__()
              if (lv_fe_i.kind.name == 'AssertPropertyStatement'):
            '''

def REUSE_NO_TDEF_IN_MOD(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'TypedefDeclaration'):
        lv_tdef_s = lv_mod_mem_i.__str__() 
        msg = 'A typedef was found inside a module'
        msg += ' This prevents reuse as the enum/typedef scope is module only'
        msg += ' An assertion model that binds to this module'
        msg += ' and check the states using the typedef will be harder'
        msg += ' to implement in such cases.'
        msg += ' Please move the typedef to a package'
        msg += ' and import that package inside the module'
        msg += str(lv_tdef_s)
        lv_rule_id = 'REUSE_NO_TDEF_IN_MOD'
        pyslint_msg(lv_rule_id, msg)

class_count = []

def REUSE_ONE_CL_PER_FILE (lv_m):
  if (lv_m.kind.name == 'ClassDeclaration'):
    for cl_rep in lv_m:
      if (cl_rep.kind.name == 'EndClassKeyword'):
        class_count.append(cl_rep.kind.name)
        continue
      elif len(class_count) > 1:
        msg = 'Always use one-class definition per file'
        lv_rule_id = 'REUSE_ONE_CL_PER_FILE'
        pyslint_msg (lv_rule_id, msg)

mod_count = []

def REUSE_ONE_MOD_PER_FILE (lv_m):
  if (lv_m.kind.name == 'ModuleDeclaration'):
    for mod_rep in lv_m.header:
      if (mod_rep.kind.name == 'ModuleKeyword'):
        mod_count.append(mod_rep.kind.name)
        continue
      elif len(mod_count) > 1:
        msg = 'Always use one-module definition per file'
        lv_rule_id = 'REUSE_ONE_MOD_PER_FILE'
        pyslint_msg (lv_rule_id, msg)
        break

def chk_dpi_rules_common(lv_dpi_scope):
  COMPAT_DPI_OLD_SPECSTR (lv_dpi_scope)
  COMPAT_DPI_NO_PURE_TASK(lv_dpi_scope)
  COMPAT_DPI_NO_MDA(lv_dpi_scope)
  FUNC_DPI_NO_4STATE_IN_RETURN (lv_dpi_scope)
  FUNC_DPI_NO_4STATE_IN_ARGS (lv_dpi_scope)
  FUNC_DPI_FN_MISSING_RTYPE(lv_dpi_scope)

def chk_dpi_rules(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'DPIExport'):
    chk_dpi_rules_common(lv_cu_scope)
  if (lv_cu_scope.kind.name == 'DPIImport'):
    chk_dpi_rules_common(lv_cu_scope)

  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'DPIExport'):
        chk_dpi_rules_common(lv_mod_mem_i)
      if (lv_mod_mem_i.kind.name == 'DPIImport'):
        chk_dpi_rules_common(lv_mod_mem_i)

  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    for lv_if_mem_i in lv_cu_scope.members:
      if (lv_if_mem_i.kind.name == 'DPIExport'):
        chk_dpi_rules_common(lv_if_mem_i)
      if (lv_if_mem_i.kind.name == 'DPIImport'):
        chk_dpi_rules_common(lv_if_mem_i)

  if (lv_cu_scope.kind.name == 'PackageDeclaration'):
    for lv_pkg_mem_i in lv_cu_scope.members:
      if (lv_pkg_mem_i.kind.name == 'DPIExport'):
        chk_dpi_rules_common(lv_pkg_mem_i)
      if (lv_pkg_mem_i.kind.name == 'DPIImport'):
        chk_dpi_rules_common(lv_pkg_mem_i)


def VLT_NO_CB_IN_INTF(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    for lv_intf_mem_i in lv_cu_scope.members:
      if (lv_intf_mem_i.kind.name == 'ClockingDeclaration'):
        msg = 'Verilator does not (fully) support clocking block \n'
        msg += '\t based drives. So avoid them for Verilator compatible'
        msg += ' testbenches. Add them inside `ifndef VERILATOR macro.'
        msg += str(lv_intf_mem_i)
        lv_rule_id = 'VLT_NO_CB_IN_INTF'
        pyslint_msg(lv_rule_id, msg)

def chk_naming(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    lv_ident_name = str(lv_cu_scope.name)
    lv_exp_s = sv_suffix_d['class']
    chk_name_style_suffix ('NAME_CLASS_SUFFIX', lv_ident_name, lv_exp_s)

  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    lv_ident_name = str(lv_cu_scope.header.name)
    lv_exp_s = sv_suffix_d['intf']
    chk_name_style_suffix ('NAME_INTF_SUFFIX', lv_ident_name, lv_exp_s)
    FUNC_NO_2STATE_IN_INTF(lv_cu_scope)

  NAME_CG_PREFIX(lv_cu_scope)

args = pyslint_argparse()

sv_prefix_d = pyslint_update_prefixes()
sv_suffix_d = pyslint_update_suffixes()
pyslint_rules_l = pyslint_update_rule_ids()

inp_test_name = args.test

tree = pyslang.SyntaxTree.fromFile(inp_test_name)
r = tree.root

if (tree.root.members.__str__() == ''):
  print("PySlint: No modules/interfaces/classes found")
  exit(0)

for scope_i in (tree.root.members):
  chk_naming(scope_i)
  chk_dpi_rules(scope_i)

  CL_METHOD_NOT_EXTERN(scope_i)
  COMPAT_PRE_RAND_NON_VOID(scope_i)
  COMPAT_POST_RAND_NON_VOID(scope_i)
  FUNC_CNST_MISSING_CAST(scope_i)
  FUNC_CNST_WRONG_OPER_PRI(scope_i)
  DBG_CL_MISSING_ENDLABEL(scope_i)
  REUSE_NO_TDEF_IN_MOD(scope_i)
  COMPAT_SVA_NO_CONC_IN_FE(scope_i)
  COMPAT_SVA_NO_EXPECT_EXPR_IN_INIT(scope_i)
  COMPAT_CG_OPT_PI_CL(scope_i)
  REUSE_CG_NO_ILBINS_CL(scope_i)
  PERF_CG_NO_ABIN_W_DEF_CL(scope_i)
  REUSE_NO_WILDC_AA_CL(scope_i)
  REUSE_ONE_CL_PER_FILE(scope_i)
  REUSE_ONE_MOD_PER_FILE(scope_i)
  FUNC_NO_BEGIN_IN_TIMING_CTRL(scope_i)
  DBG_AVOID_BEGIN_IN_TASK(scope_i)
  DBG_AVOID_BEGIN_IN_FN(scope_i)
  FUNC_NO_INIT_OF_STATIC_VAR_IN_SFN(scope_i)
  COMPAT_VAR_DINIT_IN_SFN(scope_i)
  COMPAT_NO_REF_IN_STATIC_FN(scope_i)
  VLT_NO_GENERIC_MBX(scope_i)
  VLT_NO_CB_IN_INTF(scope_i)

cu_scope = tree.root.members[0]
if (cu_scope.kind.name != 'ClassDeclaration'):
  if (hasattr(cu_scope, 'members')):
    for m_i in (cu_scope.members):
      NAME_AST_PREFIX(m_i)
      NAME_ASM_PREFIX(m_i)
      NAME_COV_PREFIX(m_i)
      FUNC_SVA_MISSING_FAIL_AB(m_i)
      PERF_SVA_NO_PASS_AB(m_i)
      NAME_PROP_PREFIX(m_i)
      COMPAT_SVA_NO_DEGEN_CONSEQ(m_i)
      COMPAT_SVA_PROP_MISSING_SEMI(m_i)
      COMPAT_SVA_NO_DEGEN_AST(m_i)
      COMPAT_SVA_NO_S_UNTIL_WITH(m_i)
      DBG_SVA_MISSING_ENDLABEL(m_i)
      NAME_CG_PREFIX(m_i)
  
