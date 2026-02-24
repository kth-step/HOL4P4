#This python script is meant to take the file that is exported by ott
#and replace ascope with a polymorphic type, and in doing so handling
#all the technical consequences that makes HOL4 accept the result 
from collections import OrderedDict
import os

filename = os.path.dirname(os.path.realpath(__file__)) + os.sep + "p4Script.sml"

#Ott-generated type abbreviations and Hol_datatypes that contain polymorphic types
#TODO Perform a check that these lines are unchanged in the p4Script.sml file?
od_hacks = OrderedDict([("Type ascope = ``:('a)``", ""), #Delete this type abbreviation
                        ("val _ = Hol_datatype ` \nffblock =  (* fixed-function block *)\n   ffblock_ff of ff\n`;",
                         "val _ = Hol_datatype ` \nffblock =  (* fixed-function block *)\n   ffblock_ff of 'a ff\n`;"),
                        ("Type ffblock_map = ``:((string, ffblock) alist)``",
                         "Type ffblock_map = ``:((string, 'a ffblock) alist)``"),
                        #TODO: Handled below?
                        ("Type actx = ``:(ab_list # pblock_map # ffblock_map # input_f # output_f # copyin_pbl # copyout_pbl # apply_table_f # ext_map # func_map # get_oracle_index # set_oracle_index # random_oracle)``",
                         "Type actx = ``:(ab_list # pblock_map # 'a ffblock_map # 'a input_f # 'a output_f # 'a copyin_pbl # 'a copyout_pbl # 'a apply_table_f # 'a ext_map # func_map # 'a get_oracle_index # 'a set_oracle_index # random_oracle)``"),
                        ("Type astate = ``:(aenv # g_scope_list # arch_frame_list # status)``",
                         "Type astate = ``:('a aenv # g_scope_list # arch_frame_list # status)``"),
                        ("Type ext_fun_map = ``:((string, ((string # d) list # ext_fun)) alist)``",
                         "Type ext_fun_map = ``:((string, ((string # d) list # 'a ext_fun)) alist)``"),
                        ("Type ext_map = ``:((string, ((((string # d) list # ext_fun) option) # ext_fun_map)) alist)``",
                         "Type ext_map = ``:((string, ((((string # d) list # 'a ext_fun) option) # 'a ext_fun_map)) alist)``"),
                        ("Type ctx = ``:(apply_table_f # ext_map # func_map # b_func_map # pars_map # tbl_map # get_oracle_index # set_oracle_index # random_oracle)``",
                         "Type ctx = ``:('a apply_table_f # 'a ext_map # func_map # b_func_map # pars_map # tbl_map # 'a get_oracle_index # 'a set_oracle_index # random_oracle)``"),
                        ("Type ectx = ``:(apply_table_f # ext_map # func_map # b_func_map # pars_map # tbl_map # i # random_oracle)``",
                         "Type ectx = ``:('a apply_table_f # 'a ext_map # func_map # b_func_map # pars_map # tbl_map # i # random_oracle)``"),
                        ("Type actx = ``:(ab_list # pblock_map # ffblock_map # input_f # output_f # copyin_pbl # copyout_pbl # apply_table_f # ext_map # func_map # 'a get_oracle_index # 'a set_oracle_index # random_oracle)``",
                         "Type actx = ``:(ab_list # pblock_map # 'a ffblock_map # 'a input_f # 'a output_f # 'a copyin_pbl # 'a copyout_pbl # 'a apply_table_f # 'a ext_map # func_map # 'a get_oracle_index # 'a set_oracle_index # random_oracle)``")
                        ])

#Assign the polymorphic types (found in semantics definitions, et.c.) a proper 'a
od = OrderedDict([("ascope_ty", "'a"), #Replace this as it appears in type abbreviations
                  (":ascope", ":'a"),
                  (":astate", ":'a astate"),
                  (":ffblock_map", ":'a ffblock_map"), 
                  (":input_f", ":'a input_f"),
                  (":output_f", ":'a output_f"),
                  (":copyin_pbl", ":'a copyin_pbl"),
                  (":copyout_pbl", ":'a copyout_pbl"),
                  (":ff", ":'a ff"),
                  (":ectx", ":'a ectx"),
                  (":ctx", ":'a ctx"),
                  (":ext_map", ":'a ext_map"),
                  (":ext_fun", ":'a ext_fun"),
                  (":get_oracle_index", ":'a get_oracle_index"),
                  (":set_oracle_index", ":'a set_oracle_index"),
                  (":apply_table_f", ":'a apply_table_f")])
                  
all_replaces = OrderedDict(list(od_hacks.items()) + list(od.items()))

def replace_all(text, dic):
    for i, j in dic.items():
        text = text.replace(i, j)
    return text

fin = open(filename, "rt")
data = fin.read()

#Replace all occurrences of the required string
data = replace_all(data, all_replaces)

fin.close()

#Output the result
fout = open(filename, "wt")
fout.write(data)
fout.close()
