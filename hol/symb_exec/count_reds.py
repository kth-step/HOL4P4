import re
import sys

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
pattern = re.compile('Reducing[ ]([^.]*?)\.\.\..*?in[ ](\d+?)[ ]ms', re.MULTILINE|re.DOTALL)

print_result(reds_count(data,pattern))

file.close()
