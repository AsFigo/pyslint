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
  lv_sv_ruleid_l.append ('FILE_NAME_CHECK_MODULE')
  lv_sv_ruleid_l.append ('FILE_NAME_CHECK_CLASS')
  lv_sv_ruleid_l.append ('CHECK_TRAILING_SPACE')

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

def cnst_arr_method_cast (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):
      if (cl_item.kind.name == 'ConstraintDeclaration'):
        for lv_cnst_i in (cl_item.block.items):
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

def chk_class_based_file_name (lv_rule_id, lv_name, lv_exp_p):
  if (lv_name == inp_test_name):
    print ('AF: Class and File names are matching: ', lv_name)
  else:
    msg = 'Improper File name : ' 
    msg += inp_test_name
    msg += ' Expected File name '
    msg += lv_exp_p
    pyslint_msg (lv_rule_id, msg)

def chk_module_based_file_name(lv_rule_id, lv_name, lv_exp_p):
  if (lv_name == inp_test_name):
    print ('AF: Class and File names are matching: ', lv_name)
  else:
    msg = 'Improper File name :' 
    msg += inp_test_name
    msg += ' Expected File name '
    msg += lv_exp_p
    pyslint_msg (lv_rule_id, msg)

def chk_naming (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    lv_ident_name = str(lv_cu_scope.name)
    lv_exp_s = sv_suffix_d['class']
    chk_name_style_suffix ('NAME_CLASS_SUFFIX', lv_ident_name, lv_exp_s)

  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    lv_ident_name = str(lv_cu_scope.header.name)
    lv_exp_s = sv_suffix_d['intf']
    chk_name_style_suffix ('NAME_INTF_SUFFIX', lv_ident_name, lv_exp_s)

  cg_label_chk (lv_cu_scope)

def chk_file_name(lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'): 
    lv_ident_name =str(lv_cu_scope.name)
    lv_exp_s='af_'+lv_ident_name+'.'+'sv'
    chk_class_based_file_name ('FILE_NAME_CHECK_CLASS', lv_ident_name, lv_exp_s)
  else: 
    if(lv_cu_scope.kind.name != 'FunctionDeclaration'):
      lv_ident_name =str(lv_cu_scope.header.name)
      lv_exp_s='af_'+lv_ident_name+'.'+'sv'
      chk_module_based_file_name('FILE_NAME_CHECK_MODULE', lv_ident_name, lv_exp_s)

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

with open(inp_test_name, 'r') as file:
    lines = file.readlines()

for i, line in enumerate(lines, start=1):
#Spliting string and white space and endswith make sure it has trailing space
    if line.rstrip('\n').endswith(' '):
        print("Following line has a trailing whitespace")
        print(f"Line {i}: {line.rstrip()}")

for scope_i in (tree.root.members):
  chk_naming (scope_i)
  use_extern (scope_i)
  cnst_arr_method_cast (scope_i)
  cl_endlabel_chk (scope_i)
  chk_file_name (scope_i)


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

