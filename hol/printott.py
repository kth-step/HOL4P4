# Python program to print cumbersome-to-write parts of the p4 ott specification

#The maximum bit-string size
max = 128

# print word wrappers
for i in range(2, max+1):
	print("Definition w%d_def:" % (i))
	print("  w%d w = ((w2v:%d word -> bool list) w,%d)" % (i, i, i))
	print("End")
	print("")
 
# print bitv_unop stuff
print("val bitv_unop_def = Define `")
print("    (bitv_unop unop (v, 1) = (w2v ((get_word_unop unop) ((v2w v): 1 word)), 1) )")
for i in range(2, max+1):
	print("/\  (bitv_unop unop (v, %d) = (w2v ((get_word_unop unop) ((v2w v): %d word)), %d) )" % (i, i, i))
print("`;")
print("")

# print bitv_binop_inner stuff
print("val bitv_binop_inner_def = Define `")
print("    (bitv_binop_inner binop v v' 1 = SOME (w2v ((get_word_binop binop) ((v2w v): 1 word) ((v2w v'): 1 word)), 1) )")
for i in range(2, max+1):
	print("/\  (bitv_binop_inner binop v v' %d = SOME (w2v ((get_word_binop binop) ((v2w v): %d word) ((v2w v'): %d word)), %d) )" % (i, i, i, i))
print("/\  (bitv_binop_inner binop v v' _ = NONE )")
print("`;")
print("")

# print bitv_binpred_inner stuff
print("val bitv_binpred_inner_def = Define `")
print("    (bitv_binpred_inner binpred v v' 1 = SOME (((get_word_binpred binpred) ((v2w v): 1 word) ((v2w v'): 1 word)):boolv) )")
for i in range(2, max+1):
	print("/\  (bitv_binpred_inner binpred v v' %d = SOME (((get_word_binpred binpred) ((v2w v): %d word) ((v2w v'): %d word)):boolv) )" % (i, i, i))
print("/\  (bitv_binpred_inner binpred v v' _ = NONE )")
print("`;")
print("")
