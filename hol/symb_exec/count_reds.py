"""
This script is used to analyze verbose output of the P4 symbolic executor.

Copy-paste the output in the HOL4 REPL to a log file, then run this script on the file.
Make sure to not accidentally copy over results from multiple runs.

Usage: python3 count_reds.py [logfile]
"""


import re
import sys

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

def print_result(dct):
    tot_time = 0
    for type, (n,t) in dct.items():
        tot_time += t
    print(string_time(tot_time)+"total running time. Individual reductions:")
    for type, (n,t) in dct.items():
        print(type+": "+str(n)+" "+" ("+string_time(t)+"total, "+string_time(t/n)+"average reduction time)")

file = open(sys.argv[1],"r")
data = file.read()
# For regular reductions, line of text after periods cannot start with "S" as in "Shortcutting"
pattern = re.compile('Reducing[ ]([^.]*?)\.\.\.\s\s[^S].*?in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

# For shortcutting, line of text after periods cannot start with "e" as in "eval-in-ctxt"
pattern2 = re.compile('Reducing[ ][^.]*?\.\.\.\s\s[^e].*?(\d+?):.*?in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

res_dict = reds_count(data,pattern)

res_dict.update(shortcut_count(data,pattern2))

print_result(res_dict)

file.close()
