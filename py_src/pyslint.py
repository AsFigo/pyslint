# ----------------------------------------------------
# SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
#                         AsFigo Technologies, UK
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

import pyslang
import argparse
import tomli

print_verbose = False

def pyslint_update_rule_ids():
  lv_sv_ruleid_l = list()
  lv_sv_ruleid_l.append ('NAME_INTF_SUFFIX')
  lv_sv_ruleid_l.append ('NAME_CLASS_SUFFIX')
  lv_sv_ruleid_l.append ('NAME_CNST_SUFFIX')
  lv_sv_ruleid_l.append ('NAME_CG_PREFIX')
  lv_sv_ruleid_l.append ('NAME_CP_PREFIX')
  lv_sv_ruleid_l.append ('NAME_CR_PREFIX')
  lv_sv_ruleid_l.append ('NAME_PROP_PREFIX')
  lv_sv_ruleid_l.append ('NAME_AST_PREFIX')
  lv_sv_ruleid_l.append ('NAME_ASM_PREFIX')
  lv_sv_ruleid_l.append ('NAME_COV_PREFIX')
  lv_sv_ruleid_l.append ('SVA_MISSING_FAIL_AB')
  lv_sv_ruleid_l.append ('SVA_MISSING_LABEL')
  lv_sv_ruleid_l.append ('SVA_MISSING_ENDLABEL')
  lv_sv_ruleid_l.append ('SVA_NO_PASS_AB')
  lv_sv_ruleid_l.append ('CL_METHOD_NOT_EXTERN')
  lv_sv_ruleid_l.append ('CL_MISSING_ENDLABEL')
  lv_sv_ruleid_l.append ('PERF_CG_TOO_MANY_CROSS')
  lv_sv_ruleid_l.append ('FUNC_CNST_MISSING_CAST')
  lv_sv_ruleid_l.append ('FUNC_CNST_DIST_COL_EQ')

'''
with open("cfg.toml", mode="rb") as fp:
  config = tomli.load(fp)
  #print (config)
'''

def pyslint_rule_enabled (rule_id):
  return True

def pyslint_msg (rule_id, msg):
  if (pyslint_rule_enabled(rule_id)):
    pyslint_str = 'PySlint: Violation: ['
    pyslint_str += rule_id
    pyslint_str += ']: '
    pyslint_str += msg 
    print (pyslint_str)

#PySlint: Error Use extern methods
def use_extern (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):

      if (cl_item.kind.name == 'ClassMethodDeclaration'):
        if (cl_item.declaration.prototype.name.kind.name != 'ConstructorName'):
            msg = 'method is not declared extern: '+ str(cl_item.declaration.prototype.name)
            pyslint_msg ('CL_METHOD_NOT_EXTERN', msg)

def af_cnst_dist_chk (cnst_i):
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
          pyslint_msg ('FUNC_CNST_DIST_COL_EQ', msg)

def cnst_arr_method_cast (lv_cu_scope):
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
            af_cnst_dist_chk (lv_cnst_i)
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
              pyslint_msg ('FUNC_CNST_MISSING_CAST', msg)


def cg_label_chk (lv_m):
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
          pyslint_msg ('NAME_CG_PREFIX', msg)

  if (lv_m.kind.name == 'CovergroupDeclaration'):
    lv_cg_name =  lv_m.name.valueText
    lv_exp_s = 'cg_'
    if (not lv_cg_name.startswith(lv_exp_s)):
      msg = 'Improper naming of identifier: ' 
      msg += lv_cg_name
      msg += ': expected prefix: '
      msg += lv_exp_s
      pyslint_msg ('NAME_CG_PREFIX', msg)


def sva_con_assert_label_chk (lv_m):

  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      msg = 'Unnamed assertion - use a meaningful label: ' 
      msg += str(lv_m.statement)
      pyslint_msg ('SVA_MISSING_LABEL', msg)
    else:
      lv_label = lv_m.statement.label.name.value
      lv_sva_vdir = lv_m.statement.keyword.valueText
      if (lv_sva_vdir != 'assert'):
        return

      lv_exp_s = sv_prefix_d['assert']
      if (not lv_label.startswith(lv_exp_s)):
        msg = 'Improper naming of assert directive: ' 
        msg += lv_label
        msg += ': expected prefix: '
        msg += lv_exp_s
        pyslint_msg ('NAME_AST_PREFIX', msg)

def sva_con_assume_label_chk (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      msg = 'Unnamed assumption - use a meaningful label: ' 
      msg += str(lv_m.statement)
      pyslint_msg ('SVA_MISSING_LABEL', msg)
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
        pyslint_msg ('NAME_ASM_PREFIX', msg)

def sva_con_cover_label_chk (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      msg = 'Unnamed assumption - use a meaningful label: ' 
      msg += str(lv_m.statement)
      pyslint_msg ('SVA_MISSING_LABEL', msg)
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
        pyslint_msg ('NAME_COV_PREFIX', msg)

def sva_prop_label_chk (lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration'):
    lv_prop_label = lv_m.name.valueText
    lv_exp_s = sv_prefix_d['prop']
    if (not lv_prop_label.startswith(lv_exp_s)):
      msg = 'Improper naming of property: ' 
      msg += lv_prop_label
      msg += ': expected prefix: '
      msg += lv_exp_s
      pyslint_msg ('NAME_PROP_PREFIX', msg)

def sva_prop_endlabel_chk (lv_m):
  if (lv_m.kind.name == 'PropertyDeclaration'):
    if (lv_m.endBlockName is None):
      lv_prop_label = lv_m.name.valueText
      msg = 'Missing End Label for property: ' 
      msg += lv_prop_label
      pyslint_msg ('SVA_MISSING_ENDLABEL', msg)

def cl_endlabel_chk (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    if (lv_cu_scope.endBlockName is None):
      lv_cl_label = lv_cu_scope.name.valueText
      msg = 'Missing End Label for class: ' 
      msg += lv_cl_label
      pyslint_msg ('CL_MISSING_ENDLABEL', msg)




def sva_con_assert_no_pass_ab_chk (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.action.statement is None):
      return
    if (lv_m.statement.action.statement.kind.name == 'EmptyStatement'):
      return

    if (lv_m.statement.action.statement is not None):
      msg = 'Avoid using PASS Action block - likely to cause too many vacuous prints: ' 
      msg += str(lv_m.statement)
      pyslint_msg ('SVA_NO_PASS_AB', msg)

def sva_con_assert_fail_ab_chk (lv_m):
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
      pyslint_msg ('SVA_MISSING_FAIL_AB', msg)

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

def chk_name_style_prefix (lv_rule_id, lv_name, lv_exp_p):
  if (lv_name.startswith(lv_exp_p)):
    if (print_verbose):
      print ('AF: Good naming: ', lv_name)
  else:
    msg = 'Improper naming of identifier: ' 
    msg += lv_name
    msg += ': expected prefix: '
    msg += lv_exp_s
    pyslint_msg (lv_rule_id, msg)

def chk_name_style_suffix (lv_rule_id, lv_name, lv_exp_s):
  if (lv_name.endswith(lv_exp_s)): 
    if (print_verbose):
      print ('AF: Good naming: ', lv_name)
  else:
    msg = 'Improper naming of identifier: ' 
    msg += lv_name
    msg += ': expected suffix: '
    msg += lv_exp_s
    pyslint_msg (lv_rule_id, msg)


def chk_intf_4state (lv_intf_scope):
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
        pyslint_msg (lv_rule_id, msg)


def chk_dpi_rval_2st (lv_dpi_mem):
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
    pyslint_msg (lv_rule_id, msg)

def chk_dpi_spec_str (lv_dpi_mem):
  lv_spec_str_val_s = lv_dpi_mem.specString.__str__().strip()
  if (lv_spec_str_val_s != '\"DPI-C\"'):
    msg = 'Wrong Spec-STR in DPI declaration'
    msg += ' IEEE 1800-2012 specifies \"DPI-C\" as Spec-STR.'
    msg += ' Found code as: \n'
    msg += str(lv_dpi_mem)
    lv_rule_id = 'COMPAT_DPI_OLD_SPECSTR'
    pyslint_msg (lv_rule_id, msg)


def chk_mod_typedef (lv_cu_scope):
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
        pyslint_msg (lv_rule_id, msg)

def chk_dpi_rules (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ModuleDeclaration'):
    for lv_mod_mem_i in lv_cu_scope.members:
      if (lv_mod_mem_i.kind.name == 'DPIImport'):
        chk_dpi_spec_str (lv_mod_mem_i)
        chk_dpi_rval_2st (lv_mod_mem_i)


def chk_naming (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    lv_ident_name = str(lv_cu_scope.name)
    lv_exp_s = sv_suffix_d['class']
    chk_name_style_suffix ('NAME_CLASS_SUFFIX', lv_ident_name, lv_exp_s)

  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    lv_ident_name = str(lv_cu_scope.header.name)
    lv_exp_s = sv_suffix_d['intf']
    chk_name_style_suffix ('NAME_INTF_SUFFIX', lv_ident_name, lv_exp_s)
    chk_intf_4state (lv_cu_scope)

  cg_label_chk (lv_cu_scope)


args = pyslint_argparse()

sv_prefix_d = pyslint_update_prefixes()
sv_suffix_d = pyslint_update_suffixes()
pyslint_rules_l = pyslint_update_rule_ids()

inp_test_name = args.test

tree = pyslang.SyntaxTree.fromFile(inp_test_name)
r = tree.root


if (tree.root.members.__str__() == ''):
  print ("PySlint: No modules/interfaces/classes found")
  exit (0)


for scope_i in (tree.root.members):
  chk_naming (scope_i)
  use_extern (scope_i)
  cnst_arr_method_cast (scope_i)
  cl_endlabel_chk (scope_i)
  chk_dpi_rules (scope_i)
  chk_mod_typedef (scope_i)


cu_scope = tree.root.members[0]
if (cu_scope.kind.name != 'ClassDeclaration'):
  for m_i in (cu_scope.members):
    sva_con_assert_label_chk (m_i)
    sva_con_assume_label_chk (m_i)
    sva_con_cover_label_chk (m_i)
    sva_con_assert_fail_ab_chk (m_i)
    sva_con_assert_no_pass_ab_chk (m_i)
    sva_prop_label_chk (m_i)
    sva_prop_endlabel_chk (m_i)
    cg_label_chk (m_i)

