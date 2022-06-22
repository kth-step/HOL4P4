#This python script is meant to take the file that is exported by ott
#and replace ascope with a polymorphic type, and in doing so handling
#all the technical consequences that makes HOL4 accept the result 
from collections import OrderedDict
import os

filename = os.path.dirname(os.path.realpath(__file__)) + os.sep + "p4Script.sml"

#Hacky, fragile rewrites
#TODO Perform a check that these lines are unchanged in the p4Script.sml file?
od_hacks = OrderedDict([("val _ = type_abbrev(\"ascope\", ``:('a)``);", ""),
                        ("val _ = Hol_datatype ` \nffblock =  (* fixed-function block *)\n   ffblock_ff of ff\n`;",
                         "val _ = Hol_datatype ` \nffblock =  (* fixed-function block *)\n   ffblock_ff of 'a ff\n`;"),
                        ("val _ = type_abbrev(\"ffblock_map\", ``:(string |-> ffblock)``);",
                         "val _ = type_abbrev(\"ffblock_map\", ``:(string |-> 'a ffblock)``);"),
                        ("val _ = type_abbrev(\"actx\", ``:(ab_list # pblock_map # ffblock_map # input_f # output_f # copyin_pbl # copyout_pbl # ext_map # func_map)``);",
                         "val _ = type_abbrev(\"actx\", ``:(ab_list # pblock_map # 'a ffblock_map # 'a input_f # 'a output_f # 'a copyin_pbl # 'a copyout_pbl # ext_map # func_map)``);")])

#Straightforward, modular rewrites
od = OrderedDict([("ascope_ty", "'a"),
                  (":ascope", ":'a"),
                  (":ffblock_map", ":'a ffblock_map"), 
                  (":input_f", ":'a input_f"),
                  (":output_f", ":'a output_f"),
                  (":copyin_pbl", ":'a copyin_pbl"),
                  (":copyout_pbl", ":'a copyout_pbl"),
                  (":ff", ":'a ff")])
                  
all_replaces = OrderedDict(list(od_hacks.items()) + list(od.items()))

def replace_all(text, dic):
    for i, j in dic.items():
        text = text.replace(i, j)
    return text

fin = open(filename, "rt")
data = fin.read()

#replace all occurrences of the required string
data = replace_all(data, all_replaces)

fin.close()

#output the result
fout = open(filename, "wt")
fout.write(data)
fout.close()
