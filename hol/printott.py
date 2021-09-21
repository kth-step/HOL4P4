# Python program to print cumbersome-to-write parts of the p4 ott specification

#The maximum word size
max = 64
 
# print intv_unop stuff
print("val intv_unop_def = Define `")
print("    (intv_unop unop (v, 1) = (w2v ((get_word_unop unop) ((v2w v): 1 word)), 1) )")
for i in range(2, max+1):
	print("/\  (intv_unop unop (v, %d) = (w2v ((get_word_unop unop) ((v2w v): %d word)), %d) )" % (i, i, i))
print("`;")
print("")

# print intv_binop_inner stuff
print("val intv_binop_inner_def = Define `")
print("    (intv_binop_inner binop v v' 1 = SOME (w2v ((get_word_binop binop) ((v2w v): 1 word) ((v2w v'): 1 word)), 1) )")
for i in range(2, max+1):
	print("/\  (intv_binop_inner binop v v' %d = SOME (w2v ((get_word_binop binop) ((v2w v): %d word) ((v2w v'): %d word)), %d) )" % (i, i, i, i))
print("/\  (intv_binop_inner binop v v' _ = NONE )")
print("`;")
print("")

# print intv_binpred_inner stuff
print("val intv_binpred_inner_def = Define `")
print("    (intv_binpred_inner binpred v v' 1 = SOME (((get_word_binpred binpred) ((v2w v): 1 word) ((v2w v'): 1 word)):boolv) )")
for i in range(2, max+1):
	print("/\  (intv_binpred_inner binpred v v' %d = SOME (((get_word_binpred binpred) ((v2w v): %d word) ((v2w v'): %d word)):boolv) )" % (i, i, i))
print("/\  (intv_binpred_inner binpred v v' _ = NONE )")
print("`;")
print("")
