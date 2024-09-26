"""
This script is used to analyze verbose output of the P4 symbolic executor.

Copy-paste the output in the HOL4 REPL to a log file, then run this script on the file.
Make sure to not accidentally copy over results from multiple runs.

Usage: python3 count_reds.py [logfile]
"""


import re
import sys

class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   BOLD = '\033[1m'
   UNDERLINE = '\033[4m'
   END = '\033[0m'

#Counts number and total time consumption for regular reductions
def reds_count(string,pattern):
    d = {}
    for match in pattern.finditer(string):
        try:
            type = match.group(1)
            time = match.group(2)
            (n, t) = d.get(type) or (0,0)
            d[type] = (n + 1, t + int(time))
        except KeyError:
            d[type] = d[type]
    return d

#Counts number and total time consumption for shortcuts
def shortcut_count(string,pattern):
    d = {}
    for match in pattern.finditer(string):
        try:
            number = match.group(1)
            time = match.group(2)
            (n, t) = d.get("shortcut") or (0,0)
            d["shortcut"] = (n + int(number), t + int(time))
        except KeyError:
            d["shortcut"] = d["shortcut"]
    return d

def string_time(time_ms):
    if time_ms == 0:
        return "0ms "
    rest, ms = divmod(int(time_ms), 1000)
    rest, s = divmod(rest, 60)
    rest, m = divmod(rest, 60)
    rest, h = divmod(rest, 60)
    if ms == 0:
        ms_str = ""
    else:
        ms_str = str(ms)+"ms "
    if s == 0:
        s_str = ""
    else:
        s_str = str(s)+"s "
    if m == 0:
        m_str = ""
    else:
        m_str = str(m)+"m "
    if h == 0:
        h_str = ""
    else:
        h_str = str(h)+"h "
    return (h_str+m_str+s_str+ms_str)

def print_result(name, dct):
    tot_time = 0
    for type, (n,t) in dct.items():
        tot_time += t
    print(string_time(tot_time)+"total time for "+name+". This consists of:")
    for type, (n,t) in dct.items():
        print(type+": "+str(n)+" "+" ("+string_time(t)+"total, "+string_time(t/n)+"on average)")

file = open(sys.argv[1],"r")
data = file.read()

# For regular reductions, line of text after periods cannot start with "S" as in "Shortcutting"
pattern = re.compile('Reducing[ ]([^.]*?)\.\.\.\s\s[^S].*?in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# For shortcutting, line of text after periods cannot start with "e" as in "eval-in-ctxt"
pattern2 = re.compile('Reducing[ ][^.]*?\.\.\.\s\s[^e].*?(\d+?):.*?in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# Symbolic branch decision computation
pattern3 = re.compile('Computing[ ][^.]*?\.\.\.\s\sFinished (.*?) in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# Symbolic branch
# TODO: Remove colon after "in"
pattern4 = re.compile('Performing[ ][^.]*?\.\.\.\s\s[^e].*?Finished (.*?) in:[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# Path tree update
# TODO: Remove colon after "in"
pattern5 = re.compile('Updating[ ][^.]*?\.\.\.\s\sFinished (.*?)[ ]in:[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# Total running time
pattern6 = re.compile('Total time consumption:[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)
total = pattern6.search(data)

print(color.BOLD + "Total running time: " + string_time(total.group(1)) + color.END)

print(color.BOLD + "Symbolic execution stage:" + color.END)

res_dict = reds_count(data,pattern)
res_dict.update(shortcut_count(data,pattern2))

#Miscellaneous operations
misc_dict = reds_count(data,pattern3)
misc_dict.update(reds_count(data,pattern4))
misc_dict.update(reds_count(data,pattern5))

# TODO: Read the other parts of the result

res_dict = dict(reversed(sorted(res_dict.items(), key=lambda item: item[1][1])))
misc_dict = dict(reversed(sorted(misc_dict.items(), key=lambda item: item[1][1])))

print_result("regular reductions", res_dict)

print("")

print_result("miscellaneous computations", misc_dict)



print(color.BOLD + "Proof of postcondition for all step theorems:" + color.END)

pattern7 = re.compile('Finished proof of postcondition for all step theorems in (\d+?)s', re.MULTILINE|re.DOTALL)
post_proof = pattern7.search(data)
print(string_time(int(post_proof.group(1))*1000)+"total time.")


print(color.BOLD + "Rewriting of step theorems to contract format:" + color.END)

pattern8 = re.compile('Finished rewriting step theorems to contract format in (\d+?)s', re.MULTILINE|re.DOTALL)
rewr_proof = pattern8.search(data)
print(string_time(int(rewr_proof.group(1))*1000)+"total time.")


print(color.BOLD + "Unification of all contracts:" + color.END)

pattern9 = re.compile('Finished unification of all contracts in (\d+?)s', re.MULTILINE|re.DOTALL)
uni_proof = pattern9.search(data)
print(string_time(int(uni_proof.group(1))*1000)+"total time.")

file.close()
