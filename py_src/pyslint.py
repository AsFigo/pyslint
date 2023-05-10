import pyslang
import argparse
import tomli

print_verbose = False

def pyslint_update_rule_ids():
  lv_sv_prefix_l = list()
  lv_sv_prefix_l.append ('NAME_INTF_SUFFIX')
  lv_sv_prefix_l.append ('NAME_CLASS_SUFFIX')
  lv_sv_prefix_l.append ('NAME_CNST_SUFFIX')
  lv_sv_prefix_l.append ('NAME_CG_SUFFIX')
  lv_sv_prefix_l.append ('NAME_PROP_PREFIX')
  lv_sv_prefix_l.append ('NAME_AST_PREFIX')
  lv_sv_prefix_l.append ('NAME_ASM_PREFIX')
  lv_sv_prefix_l.append ('NAME_COV_PREFIX')
  lv_sv_prefix_l.append ('SVA_MISSING_FAIL_AB')
  lv_sv_prefix_l.append ('SVA_MISSING_LABEL')
  lv_sv_prefix_l.append ('SVA_NO_PASS_AB')
  lv_sv_prefix_l.append ('CL_METHOD_NOT_EXTERN')
  lv_sv_prefix_l.append ('PERF_CG_TOO_MANY_CROSS')

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
    # af_sv_naming_test.sv:22: Class name does not have suffix _c

#PySlint: Error Use extern methods
def use_extern (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    for cl_item in (lv_cu_scope.items):

      if (cl_item.kind.name == 'ClassMethodDeclaration'):
        if (cl_item.declaration.prototype.name.kind.name != 'ConstructorName'):
            print ('PySlint: Error method is not declared extern: ', cl_item.declaration.prototype.name)
            msg = 'method is not declared extern: '+ cl_item.declaration.prototype.name
            pyslint_msg ('CL_METHOD_NOT_EXTERN', msg)

def cg_label_chk (lv_m):
  if (lv_m.kind.name == 'CovergroupDeclaration'):
    lv_cg_name =  lv_m.name.valueText
    if (not lv_cg_name.startswith('cg_')):
          print ("PySlint: Error: Label must start with \'cg_\': ", 
          lv_cg_name)


def sva_con_assert_label_chk (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.label is None):
      print ("PySlint: Error: Unnamed SVA: ", 
              lv_m.statement)
    else:
      lv_label = lv_m.statement.label.name.value
      if (not lv_label.startswith('a')):
          print ("PySlint: Error: Label must start with \'a\': ", 
          lv_label)


def sva_con_assert_fail_ab_chk (lv_m):
  if (lv_m.kind.name == 'ConcurrentAssertionMember'):
    if (lv_m.statement.action.elseClause is None):
      print ("PySlint: Error: Missing FAIL Action block in SVA: ", 
              lv_m.statement)

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



def chk_naming (lv_cu_scope):
  if (lv_cu_scope.kind.name == 'ClassDeclaration'):
    lv_ident_name = str(lv_cu_scope.name)
    lv_exp_s = sv_suffix_d['class']
    chk_name_style_suffix ('NAME_CLASS_SUFFIX', lv_ident_name, lv_exp_s)

  if (lv_cu_scope.kind.name == 'InterfaceDeclaration'):
    lv_ident_name = str(lv_cu_scope.header.name)
    lv_exp_s = sv_suffix_d['intf']
    chk_name_style_suffix ('NAME_INTF_SUFFIX', lv_ident_name, lv_exp_s)


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


cu_scope = tree.root.members[0]
if (cu_scope.kind.name != 'ClassDeclaration'):
  for m_i in (cu_scope.members):
    sva_con_assert_label_chk (m_i)
    sva_con_assert_fail_ab_chk (m_i)
    cg_label_chk (m_i)

