open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_arithmetic_correct";

open p4Theory p4_auxTheory p4_exec_semTheory;

(* All semantics arithmetic operations in the old semantics are implemented
 * by the new semantics. *)

intLib.deprecate_int();

Definition get_word_unop_def:
  (get_word_unop unop_compl = word_1comp) /\
  (get_word_unop unop_neg_signed = word_2comp) /\
  (get_word_unop unop_un_plus = (\w. w))
End

(* Old bitv_unop *)
Definition bitv_unop_old_def:
    (bitv_unop_old unop (v, 1) = (w2v ((get_word_unop unop) ((v2w v): 1 word)), 1) )
/\  (bitv_unop_old unop (v, 2) = (w2v ((get_word_unop unop) ((v2w v): 2 word)), 2) )
/\  (bitv_unop_old unop (v, 3) = (w2v ((get_word_unop unop) ((v2w v): 3 word)), 3) )
/\  (bitv_unop_old unop (v, 4) = (w2v ((get_word_unop unop) ((v2w v): 4 word)), 4) )
/\  (bitv_unop_old unop (v, 5) = (w2v ((get_word_unop unop) ((v2w v): 5 word)), 5) )
/\  (bitv_unop_old unop (v, 6) = (w2v ((get_word_unop unop) ((v2w v): 6 word)), 6) )
/\  (bitv_unop_old unop (v, 7) = (w2v ((get_word_unop unop) ((v2w v): 7 word)), 7) )
/\  (bitv_unop_old unop (v, 8) = (w2v ((get_word_unop unop) ((v2w v): 8 word)), 8) )
/\  (bitv_unop_old unop (v, 9) = (w2v ((get_word_unop unop) ((v2w v): 9 word)), 9) )
/\  (bitv_unop_old unop (v, 10) = (w2v ((get_word_unop unop) ((v2w v): 10 word)), 10) )
/\  (bitv_unop_old unop (v, 11) = (w2v ((get_word_unop unop) ((v2w v): 11 word)), 11) )
/\  (bitv_unop_old unop (v, 12) = (w2v ((get_word_unop unop) ((v2w v): 12 word)), 12) )
/\  (bitv_unop_old unop (v, 13) = (w2v ((get_word_unop unop) ((v2w v): 13 word)), 13) )
/\  (bitv_unop_old unop (v, 14) = (w2v ((get_word_unop unop) ((v2w v): 14 word)), 14) )
/\  (bitv_unop_old unop (v, 15) = (w2v ((get_word_unop unop) ((v2w v): 15 word)), 15) )
/\  (bitv_unop_old unop (v, 16) = (w2v ((get_word_unop unop) ((v2w v): 16 word)), 16) )
/\  (bitv_unop_old unop (v, 17) = (w2v ((get_word_unop unop) ((v2w v): 17 word)), 17) )
/\  (bitv_unop_old unop (v, 18) = (w2v ((get_word_unop unop) ((v2w v): 18 word)), 18) )
/\  (bitv_unop_old unop (v, 19) = (w2v ((get_word_unop unop) ((v2w v): 19 word)), 19) )
/\  (bitv_unop_old unop (v, 20) = (w2v ((get_word_unop unop) ((v2w v): 20 word)), 20) )
/\  (bitv_unop_old unop (v, 21) = (w2v ((get_word_unop unop) ((v2w v): 21 word)), 21) )
/\  (bitv_unop_old unop (v, 22) = (w2v ((get_word_unop unop) ((v2w v): 22 word)), 22) )
/\  (bitv_unop_old unop (v, 23) = (w2v ((get_word_unop unop) ((v2w v): 23 word)), 23) )
/\  (bitv_unop_old unop (v, 24) = (w2v ((get_word_unop unop) ((v2w v): 24 word)), 24) )
/\  (bitv_unop_old unop (v, 25) = (w2v ((get_word_unop unop) ((v2w v): 25 word)), 25) )
/\  (bitv_unop_old unop (v, 26) = (w2v ((get_word_unop unop) ((v2w v): 26 word)), 26) )
/\  (bitv_unop_old unop (v, 27) = (w2v ((get_word_unop unop) ((v2w v): 27 word)), 27) )
/\  (bitv_unop_old unop (v, 28) = (w2v ((get_word_unop unop) ((v2w v): 28 word)), 28) )
/\  (bitv_unop_old unop (v, 29) = (w2v ((get_word_unop unop) ((v2w v): 29 word)), 29) )
/\  (bitv_unop_old unop (v, 30) = (w2v ((get_word_unop unop) ((v2w v): 30 word)), 30) )
/\  (bitv_unop_old unop (v, 31) = (w2v ((get_word_unop unop) ((v2w v): 31 word)), 31) )
/\  (bitv_unop_old unop (v, 32) = (w2v ((get_word_unop unop) ((v2w v): 32 word)), 32) )
/\  (bitv_unop_old unop (v, 33) = (w2v ((get_word_unop unop) ((v2w v): 33 word)), 33) )
/\  (bitv_unop_old unop (v, 34) = (w2v ((get_word_unop unop) ((v2w v): 34 word)), 34) )
/\  (bitv_unop_old unop (v, 35) = (w2v ((get_word_unop unop) ((v2w v): 35 word)), 35) )
/\  (bitv_unop_old unop (v, 36) = (w2v ((get_word_unop unop) ((v2w v): 36 word)), 36) )
/\  (bitv_unop_old unop (v, 37) = (w2v ((get_word_unop unop) ((v2w v): 37 word)), 37) )
/\  (bitv_unop_old unop (v, 38) = (w2v ((get_word_unop unop) ((v2w v): 38 word)), 38) )
/\  (bitv_unop_old unop (v, 39) = (w2v ((get_word_unop unop) ((v2w v): 39 word)), 39) )
/\  (bitv_unop_old unop (v, 40) = (w2v ((get_word_unop unop) ((v2w v): 40 word)), 40) )
/\  (bitv_unop_old unop (v, 41) = (w2v ((get_word_unop unop) ((v2w v): 41 word)), 41) )
/\  (bitv_unop_old unop (v, 42) = (w2v ((get_word_unop unop) ((v2w v): 42 word)), 42) )
/\  (bitv_unop_old unop (v, 43) = (w2v ((get_word_unop unop) ((v2w v): 43 word)), 43) )
/\  (bitv_unop_old unop (v, 44) = (w2v ((get_word_unop unop) ((v2w v): 44 word)), 44) )
/\  (bitv_unop_old unop (v, 45) = (w2v ((get_word_unop unop) ((v2w v): 45 word)), 45) )
/\  (bitv_unop_old unop (v, 46) = (w2v ((get_word_unop unop) ((v2w v): 46 word)), 46) )
/\  (bitv_unop_old unop (v, 47) = (w2v ((get_word_unop unop) ((v2w v): 47 word)), 47) )
/\  (bitv_unop_old unop (v, 48) = (w2v ((get_word_unop unop) ((v2w v): 48 word)), 48) )
/\  (bitv_unop_old unop (v, 49) = (w2v ((get_word_unop unop) ((v2w v): 49 word)), 49) )
/\  (bitv_unop_old unop (v, 50) = (w2v ((get_word_unop unop) ((v2w v): 50 word)), 50) )
/\  (bitv_unop_old unop (v, 51) = (w2v ((get_word_unop unop) ((v2w v): 51 word)), 51) )
/\  (bitv_unop_old unop (v, 52) = (w2v ((get_word_unop unop) ((v2w v): 52 word)), 52) )
/\  (bitv_unop_old unop (v, 53) = (w2v ((get_word_unop unop) ((v2w v): 53 word)), 53) )
/\  (bitv_unop_old unop (v, 54) = (w2v ((get_word_unop unop) ((v2w v): 54 word)), 54) )
/\  (bitv_unop_old unop (v, 55) = (w2v ((get_word_unop unop) ((v2w v): 55 word)), 55) )
/\  (bitv_unop_old unop (v, 56) = (w2v ((get_word_unop unop) ((v2w v): 56 word)), 56) )
/\  (bitv_unop_old unop (v, 57) = (w2v ((get_word_unop unop) ((v2w v): 57 word)), 57) )
/\  (bitv_unop_old unop (v, 58) = (w2v ((get_word_unop unop) ((v2w v): 58 word)), 58) )
/\  (bitv_unop_old unop (v, 59) = (w2v ((get_word_unop unop) ((v2w v): 59 word)), 59) )
/\  (bitv_unop_old unop (v, 60) = (w2v ((get_word_unop unop) ((v2w v): 60 word)), 60) )
/\  (bitv_unop_old unop (v, 61) = (w2v ((get_word_unop unop) ((v2w v): 61 word)), 61) )
/\  (bitv_unop_old unop (v, 62) = (w2v ((get_word_unop unop) ((v2w v): 62 word)), 62) )
/\  (bitv_unop_old unop (v, 63) = (w2v ((get_word_unop unop) ((v2w v): 63 word)), 63) )
/\  (bitv_unop_old unop (v, 64) = (w2v ((get_word_unop unop) ((v2w v): 64 word)), 64) )
/\  (bitv_unop_old unop (v, 65) = (w2v ((get_word_unop unop) ((v2w v): 65 word)), 65) )
/\  (bitv_unop_old unop (v, 66) = (w2v ((get_word_unop unop) ((v2w v): 66 word)), 66) )
/\  (bitv_unop_old unop (v, 67) = (w2v ((get_word_unop unop) ((v2w v): 67 word)), 67) )
/\  (bitv_unop_old unop (v, 68) = (w2v ((get_word_unop unop) ((v2w v): 68 word)), 68) )
/\  (bitv_unop_old unop (v, 69) = (w2v ((get_word_unop unop) ((v2w v): 69 word)), 69) )
/\  (bitv_unop_old unop (v, 70) = (w2v ((get_word_unop unop) ((v2w v): 70 word)), 70) )
/\  (bitv_unop_old unop (v, 71) = (w2v ((get_word_unop unop) ((v2w v): 71 word)), 71) )
/\  (bitv_unop_old unop (v, 72) = (w2v ((get_word_unop unop) ((v2w v): 72 word)), 72) )
/\  (bitv_unop_old unop (v, 73) = (w2v ((get_word_unop unop) ((v2w v): 73 word)), 73) )
/\  (bitv_unop_old unop (v, 74) = (w2v ((get_word_unop unop) ((v2w v): 74 word)), 74) )
/\  (bitv_unop_old unop (v, 75) = (w2v ((get_word_unop unop) ((v2w v): 75 word)), 75) )
/\  (bitv_unop_old unop (v, 76) = (w2v ((get_word_unop unop) ((v2w v): 76 word)), 76) )
/\  (bitv_unop_old unop (v, 77) = (w2v ((get_word_unop unop) ((v2w v): 77 word)), 77) )
/\  (bitv_unop_old unop (v, 78) = (w2v ((get_word_unop unop) ((v2w v): 78 word)), 78) )
/\  (bitv_unop_old unop (v, 79) = (w2v ((get_word_unop unop) ((v2w v): 79 word)), 79) )
/\  (bitv_unop_old unop (v, 80) = (w2v ((get_word_unop unop) ((v2w v): 80 word)), 80) )
/\  (bitv_unop_old unop (v, 81) = (w2v ((get_word_unop unop) ((v2w v): 81 word)), 81) )
/\  (bitv_unop_old unop (v, 82) = (w2v ((get_word_unop unop) ((v2w v): 82 word)), 82) )
/\  (bitv_unop_old unop (v, 83) = (w2v ((get_word_unop unop) ((v2w v): 83 word)), 83) )
/\  (bitv_unop_old unop (v, 84) = (w2v ((get_word_unop unop) ((v2w v): 84 word)), 84) )
/\  (bitv_unop_old unop (v, 85) = (w2v ((get_word_unop unop) ((v2w v): 85 word)), 85) )
/\  (bitv_unop_old unop (v, 86) = (w2v ((get_word_unop unop) ((v2w v): 86 word)), 86) )
/\  (bitv_unop_old unop (v, 87) = (w2v ((get_word_unop unop) ((v2w v): 87 word)), 87) )
/\  (bitv_unop_old unop (v, 88) = (w2v ((get_word_unop unop) ((v2w v): 88 word)), 88) )
/\  (bitv_unop_old unop (v, 89) = (w2v ((get_word_unop unop) ((v2w v): 89 word)), 89) )
/\  (bitv_unop_old unop (v, 90) = (w2v ((get_word_unop unop) ((v2w v): 90 word)), 90) )
/\  (bitv_unop_old unop (v, 91) = (w2v ((get_word_unop unop) ((v2w v): 91 word)), 91) )
/\  (bitv_unop_old unop (v, 92) = (w2v ((get_word_unop unop) ((v2w v): 92 word)), 92) )
/\  (bitv_unop_old unop (v, 93) = (w2v ((get_word_unop unop) ((v2w v): 93 word)), 93) )
/\  (bitv_unop_old unop (v, 94) = (w2v ((get_word_unop unop) ((v2w v): 94 word)), 94) )
/\  (bitv_unop_old unop (v, 95) = (w2v ((get_word_unop unop) ((v2w v): 95 word)), 95) )
/\  (bitv_unop_old unop (v, 96) = (w2v ((get_word_unop unop) ((v2w v): 96 word)), 96) )
/\  (bitv_unop_old unop (v, 97) = (w2v ((get_word_unop unop) ((v2w v): 97 word)), 97) )
/\  (bitv_unop_old unop (v, 98) = (w2v ((get_word_unop unop) ((v2w v): 98 word)), 98) )
/\  (bitv_unop_old unop (v, 99) = (w2v ((get_word_unop unop) ((v2w v): 99 word)), 99) )
/\  (bitv_unop_old unop (v, 100) = (w2v ((get_word_unop unop) ((v2w v): 100 word)), 100) )
/\  (bitv_unop_old unop (v, 101) = (w2v ((get_word_unop unop) ((v2w v): 101 word)), 101) )
/\  (bitv_unop_old unop (v, 102) = (w2v ((get_word_unop unop) ((v2w v): 102 word)), 102) )
/\  (bitv_unop_old unop (v, 103) = (w2v ((get_word_unop unop) ((v2w v): 103 word)), 103) )
/\  (bitv_unop_old unop (v, 104) = (w2v ((get_word_unop unop) ((v2w v): 104 word)), 104) )
/\  (bitv_unop_old unop (v, 105) = (w2v ((get_word_unop unop) ((v2w v): 105 word)), 105) )
/\  (bitv_unop_old unop (v, 106) = (w2v ((get_word_unop unop) ((v2w v): 106 word)), 106) )
/\  (bitv_unop_old unop (v, 107) = (w2v ((get_word_unop unop) ((v2w v): 107 word)), 107) )
/\  (bitv_unop_old unop (v, 108) = (w2v ((get_word_unop unop) ((v2w v): 108 word)), 108) )
/\  (bitv_unop_old unop (v, 109) = (w2v ((get_word_unop unop) ((v2w v): 109 word)), 109) )
/\  (bitv_unop_old unop (v, 110) = (w2v ((get_word_unop unop) ((v2w v): 110 word)), 110) )
/\  (bitv_unop_old unop (v, 111) = (w2v ((get_word_unop unop) ((v2w v): 111 word)), 111) )
/\  (bitv_unop_old unop (v, 112) = (w2v ((get_word_unop unop) ((v2w v): 112 word)), 112) )
/\  (bitv_unop_old unop (v, 113) = (w2v ((get_word_unop unop) ((v2w v): 113 word)), 113) )
/\  (bitv_unop_old unop (v, 114) = (w2v ((get_word_unop unop) ((v2w v): 114 word)), 114) )
/\  (bitv_unop_old unop (v, 115) = (w2v ((get_word_unop unop) ((v2w v): 115 word)), 115) )
/\  (bitv_unop_old unop (v, 116) = (w2v ((get_word_unop unop) ((v2w v): 116 word)), 116) )
/\  (bitv_unop_old unop (v, 117) = (w2v ((get_word_unop unop) ((v2w v): 117 word)), 117) )
/\  (bitv_unop_old unop (v, 118) = (w2v ((get_word_unop unop) ((v2w v): 118 word)), 118) )
/\  (bitv_unop_old unop (v, 119) = (w2v ((get_word_unop unop) ((v2w v): 119 word)), 119) )
/\  (bitv_unop_old unop (v, 120) = (w2v ((get_word_unop unop) ((v2w v): 120 word)), 120) )
/\  (bitv_unop_old unop (v, 121) = (w2v ((get_word_unop unop) ((v2w v): 121 word)), 121) )
/\  (bitv_unop_old unop (v, 122) = (w2v ((get_word_unop unop) ((v2w v): 122 word)), 122) )
/\  (bitv_unop_old unop (v, 123) = (w2v ((get_word_unop unop) ((v2w v): 123 word)), 123) )
/\  (bitv_unop_old unop (v, 124) = (w2v ((get_word_unop unop) ((v2w v): 124 word)), 124) )
/\  (bitv_unop_old unop (v, 125) = (w2v ((get_word_unop unop) ((v2w v): 125 word)), 125) )
/\  (bitv_unop_old unop (v, 126) = (w2v ((get_word_unop unop) ((v2w v): 126 word)), 126) )
/\  (bitv_unop_old unop (v, 127) = (w2v ((get_word_unop unop) ((v2w v): 127 word)), 127) )
/\  (bitv_unop_old unop (v, 128) = (w2v ((get_word_unop unop) ((v2w v): 128 word)), 128) )
End

Definition get_word_binop_def:
    (get_word_binop binop_mul = word_mul)
/\  (get_word_binop binop_div = word_div)
/\  (get_word_binop binop_mod = word_mod)
/\  (get_word_binop binop_add = word_add)
/\  (get_word_binop binop_sat_add = saturate_add)
/\  (get_word_binop binop_sub = word_sub)
/\  (get_word_binop binop_sat_sub = saturate_sub)
/\  (get_word_binop binop_shl = word_lsl_bv)
/\  (get_word_binop binop_shr = word_lsr_bv)
/\  (get_word_binop binop_and = word_and)
/\  (get_word_binop binop_xor = word_xor)
/\  (get_word_binop binop_or = word_or)
End

Definition bitv_binop_inner_def:
    (bitv_binop_inner binop v v' 1 = SOME (w2v ((get_word_binop binop) ((v2w v): 1 word) ((v2w v'): 1 word)), 1) )
/\  (bitv_binop_inner binop v v' 2 = SOME (w2v ((get_word_binop binop) ((v2w v): 2 word) ((v2w v'): 2 word)), 2) )
/\  (bitv_binop_inner binop v v' 3 = SOME (w2v ((get_word_binop binop) ((v2w v): 3 word) ((v2w v'): 3 word)), 3) )
/\  (bitv_binop_inner binop v v' 4 = SOME (w2v ((get_word_binop binop) ((v2w v): 4 word) ((v2w v'): 4 word)), 4) )
/\  (bitv_binop_inner binop v v' 5 = SOME (w2v ((get_word_binop binop) ((v2w v): 5 word) ((v2w v'): 5 word)), 5) )
/\  (bitv_binop_inner binop v v' 6 = SOME (w2v ((get_word_binop binop) ((v2w v): 6 word) ((v2w v'): 6 word)), 6) )
/\  (bitv_binop_inner binop v v' 7 = SOME (w2v ((get_word_binop binop) ((v2w v): 7 word) ((v2w v'): 7 word)), 7) )
/\  (bitv_binop_inner binop v v' 8 = SOME (w2v ((get_word_binop binop) ((v2w v): 8 word) ((v2w v'): 8 word)), 8) )
/\  (bitv_binop_inner binop v v' 9 = SOME (w2v ((get_word_binop binop) ((v2w v): 9 word) ((v2w v'): 9 word)), 9) )
/\  (bitv_binop_inner binop v v' 10 = SOME (w2v ((get_word_binop binop) ((v2w v): 10 word) ((v2w v'): 10 word)), 10) )
/\  (bitv_binop_inner binop v v' 11 = SOME (w2v ((get_word_binop binop) ((v2w v): 11 word) ((v2w v'): 11 word)), 11) )
/\  (bitv_binop_inner binop v v' 12 = SOME (w2v ((get_word_binop binop) ((v2w v): 12 word) ((v2w v'): 12 word)), 12) )
/\  (bitv_binop_inner binop v v' 13 = SOME (w2v ((get_word_binop binop) ((v2w v): 13 word) ((v2w v'): 13 word)), 13) )
/\  (bitv_binop_inner binop v v' 14 = SOME (w2v ((get_word_binop binop) ((v2w v): 14 word) ((v2w v'): 14 word)), 14) )
/\  (bitv_binop_inner binop v v' 15 = SOME (w2v ((get_word_binop binop) ((v2w v): 15 word) ((v2w v'): 15 word)), 15) )
/\  (bitv_binop_inner binop v v' 16 = SOME (w2v ((get_word_binop binop) ((v2w v): 16 word) ((v2w v'): 16 word)), 16) )
/\  (bitv_binop_inner binop v v' 17 = SOME (w2v ((get_word_binop binop) ((v2w v): 17 word) ((v2w v'): 17 word)), 17) )
/\  (bitv_binop_inner binop v v' 18 = SOME (w2v ((get_word_binop binop) ((v2w v): 18 word) ((v2w v'): 18 word)), 18) )
/\  (bitv_binop_inner binop v v' 19 = SOME (w2v ((get_word_binop binop) ((v2w v): 19 word) ((v2w v'): 19 word)), 19) )
/\  (bitv_binop_inner binop v v' 20 = SOME (w2v ((get_word_binop binop) ((v2w v): 20 word) ((v2w v'): 20 word)), 20) )
/\  (bitv_binop_inner binop v v' 21 = SOME (w2v ((get_word_binop binop) ((v2w v): 21 word) ((v2w v'): 21 word)), 21) )
/\  (bitv_binop_inner binop v v' 22 = SOME (w2v ((get_word_binop binop) ((v2w v): 22 word) ((v2w v'): 22 word)), 22) )
/\  (bitv_binop_inner binop v v' 23 = SOME (w2v ((get_word_binop binop) ((v2w v): 23 word) ((v2w v'): 23 word)), 23) )
/\  (bitv_binop_inner binop v v' 24 = SOME (w2v ((get_word_binop binop) ((v2w v): 24 word) ((v2w v'): 24 word)), 24) )
/\  (bitv_binop_inner binop v v' 25 = SOME (w2v ((get_word_binop binop) ((v2w v): 25 word) ((v2w v'): 25 word)), 25) )
/\  (bitv_binop_inner binop v v' 26 = SOME (w2v ((get_word_binop binop) ((v2w v): 26 word) ((v2w v'): 26 word)), 26) )
/\  (bitv_binop_inner binop v v' 27 = SOME (w2v ((get_word_binop binop) ((v2w v): 27 word) ((v2w v'): 27 word)), 27) )
/\  (bitv_binop_inner binop v v' 28 = SOME (w2v ((get_word_binop binop) ((v2w v): 28 word) ((v2w v'): 28 word)), 28) )
/\  (bitv_binop_inner binop v v' 29 = SOME (w2v ((get_word_binop binop) ((v2w v): 29 word) ((v2w v'): 29 word)), 29) )
/\  (bitv_binop_inner binop v v' 30 = SOME (w2v ((get_word_binop binop) ((v2w v): 30 word) ((v2w v'): 30 word)), 30) )
/\  (bitv_binop_inner binop v v' 31 = SOME (w2v ((get_word_binop binop) ((v2w v): 31 word) ((v2w v'): 31 word)), 31) )
/\  (bitv_binop_inner binop v v' 32 = SOME (w2v ((get_word_binop binop) ((v2w v): 32 word) ((v2w v'): 32 word)), 32) )
/\  (bitv_binop_inner binop v v' 33 = SOME (w2v ((get_word_binop binop) ((v2w v): 33 word) ((v2w v'): 33 word)), 33) )
/\  (bitv_binop_inner binop v v' 34 = SOME (w2v ((get_word_binop binop) ((v2w v): 34 word) ((v2w v'): 34 word)), 34) )
/\  (bitv_binop_inner binop v v' 35 = SOME (w2v ((get_word_binop binop) ((v2w v): 35 word) ((v2w v'): 35 word)), 35) )
/\  (bitv_binop_inner binop v v' 36 = SOME (w2v ((get_word_binop binop) ((v2w v): 36 word) ((v2w v'): 36 word)), 36) )
/\  (bitv_binop_inner binop v v' 37 = SOME (w2v ((get_word_binop binop) ((v2w v): 37 word) ((v2w v'): 37 word)), 37) )
/\  (bitv_binop_inner binop v v' 38 = SOME (w2v ((get_word_binop binop) ((v2w v): 38 word) ((v2w v'): 38 word)), 38) )
/\  (bitv_binop_inner binop v v' 39 = SOME (w2v ((get_word_binop binop) ((v2w v): 39 word) ((v2w v'): 39 word)), 39) )
/\  (bitv_binop_inner binop v v' 40 = SOME (w2v ((get_word_binop binop) ((v2w v): 40 word) ((v2w v'): 40 word)), 40) )
/\  (bitv_binop_inner binop v v' 41 = SOME (w2v ((get_word_binop binop) ((v2w v): 41 word) ((v2w v'): 41 word)), 41) )
/\  (bitv_binop_inner binop v v' 42 = SOME (w2v ((get_word_binop binop) ((v2w v): 42 word) ((v2w v'): 42 word)), 42) )
/\  (bitv_binop_inner binop v v' 43 = SOME (w2v ((get_word_binop binop) ((v2w v): 43 word) ((v2w v'): 43 word)), 43) )
/\  (bitv_binop_inner binop v v' 44 = SOME (w2v ((get_word_binop binop) ((v2w v): 44 word) ((v2w v'): 44 word)), 44) )
/\  (bitv_binop_inner binop v v' 45 = SOME (w2v ((get_word_binop binop) ((v2w v): 45 word) ((v2w v'): 45 word)), 45) )
/\  (bitv_binop_inner binop v v' 46 = SOME (w2v ((get_word_binop binop) ((v2w v): 46 word) ((v2w v'): 46 word)), 46) )
/\  (bitv_binop_inner binop v v' 47 = SOME (w2v ((get_word_binop binop) ((v2w v): 47 word) ((v2w v'): 47 word)), 47) )
/\  (bitv_binop_inner binop v v' 48 = SOME (w2v ((get_word_binop binop) ((v2w v): 48 word) ((v2w v'): 48 word)), 48) )
/\  (bitv_binop_inner binop v v' 49 = SOME (w2v ((get_word_binop binop) ((v2w v): 49 word) ((v2w v'): 49 word)), 49) )
/\  (bitv_binop_inner binop v v' 50 = SOME (w2v ((get_word_binop binop) ((v2w v): 50 word) ((v2w v'): 50 word)), 50) )
/\  (bitv_binop_inner binop v v' 51 = SOME (w2v ((get_word_binop binop) ((v2w v): 51 word) ((v2w v'): 51 word)), 51) )
/\  (bitv_binop_inner binop v v' 52 = SOME (w2v ((get_word_binop binop) ((v2w v): 52 word) ((v2w v'): 52 word)), 52) )
/\  (bitv_binop_inner binop v v' 53 = SOME (w2v ((get_word_binop binop) ((v2w v): 53 word) ((v2w v'): 53 word)), 53) )
/\  (bitv_binop_inner binop v v' 54 = SOME (w2v ((get_word_binop binop) ((v2w v): 54 word) ((v2w v'): 54 word)), 54) )
/\  (bitv_binop_inner binop v v' 55 = SOME (w2v ((get_word_binop binop) ((v2w v): 55 word) ((v2w v'): 55 word)), 55) )
/\  (bitv_binop_inner binop v v' 56 = SOME (w2v ((get_word_binop binop) ((v2w v): 56 word) ((v2w v'): 56 word)), 56) )
/\  (bitv_binop_inner binop v v' 57 = SOME (w2v ((get_word_binop binop) ((v2w v): 57 word) ((v2w v'): 57 word)), 57) )
/\  (bitv_binop_inner binop v v' 58 = SOME (w2v ((get_word_binop binop) ((v2w v): 58 word) ((v2w v'): 58 word)), 58) )
/\  (bitv_binop_inner binop v v' 59 = SOME (w2v ((get_word_binop binop) ((v2w v): 59 word) ((v2w v'): 59 word)), 59) )
/\  (bitv_binop_inner binop v v' 60 = SOME (w2v ((get_word_binop binop) ((v2w v): 60 word) ((v2w v'): 60 word)), 60) )
/\  (bitv_binop_inner binop v v' 61 = SOME (w2v ((get_word_binop binop) ((v2w v): 61 word) ((v2w v'): 61 word)), 61) )
/\  (bitv_binop_inner binop v v' 62 = SOME (w2v ((get_word_binop binop) ((v2w v): 62 word) ((v2w v'): 62 word)), 62) )
/\  (bitv_binop_inner binop v v' 63 = SOME (w2v ((get_word_binop binop) ((v2w v): 63 word) ((v2w v'): 63 word)), 63) )
/\  (bitv_binop_inner binop v v' 64 = SOME (w2v ((get_word_binop binop) ((v2w v): 64 word) ((v2w v'): 64 word)), 64) )
/\  (bitv_binop_inner binop v v' 65 = SOME (w2v ((get_word_binop binop) ((v2w v): 65 word) ((v2w v'): 65 word)), 65) )
/\  (bitv_binop_inner binop v v' 66 = SOME (w2v ((get_word_binop binop) ((v2w v): 66 word) ((v2w v'): 66 word)), 66) )
/\  (bitv_binop_inner binop v v' 67 = SOME (w2v ((get_word_binop binop) ((v2w v): 67 word) ((v2w v'): 67 word)), 67) )
/\  (bitv_binop_inner binop v v' 68 = SOME (w2v ((get_word_binop binop) ((v2w v): 68 word) ((v2w v'): 68 word)), 68) )
/\  (bitv_binop_inner binop v v' 69 = SOME (w2v ((get_word_binop binop) ((v2w v): 69 word) ((v2w v'): 69 word)), 69) )
/\  (bitv_binop_inner binop v v' 70 = SOME (w2v ((get_word_binop binop) ((v2w v): 70 word) ((v2w v'): 70 word)), 70) )
/\  (bitv_binop_inner binop v v' 71 = SOME (w2v ((get_word_binop binop) ((v2w v): 71 word) ((v2w v'): 71 word)), 71) )
/\  (bitv_binop_inner binop v v' 72 = SOME (w2v ((get_word_binop binop) ((v2w v): 72 word) ((v2w v'): 72 word)), 72) )
/\  (bitv_binop_inner binop v v' 73 = SOME (w2v ((get_word_binop binop) ((v2w v): 73 word) ((v2w v'): 73 word)), 73) )
/\  (bitv_binop_inner binop v v' 74 = SOME (w2v ((get_word_binop binop) ((v2w v): 74 word) ((v2w v'): 74 word)), 74) )
/\  (bitv_binop_inner binop v v' 75 = SOME (w2v ((get_word_binop binop) ((v2w v): 75 word) ((v2w v'): 75 word)), 75) )
/\  (bitv_binop_inner binop v v' 76 = SOME (w2v ((get_word_binop binop) ((v2w v): 76 word) ((v2w v'): 76 word)), 76) )
/\  (bitv_binop_inner binop v v' 77 = SOME (w2v ((get_word_binop binop) ((v2w v): 77 word) ((v2w v'): 77 word)), 77) )
/\  (bitv_binop_inner binop v v' 78 = SOME (w2v ((get_word_binop binop) ((v2w v): 78 word) ((v2w v'): 78 word)), 78) )
/\  (bitv_binop_inner binop v v' 79 = SOME (w2v ((get_word_binop binop) ((v2w v): 79 word) ((v2w v'): 79 word)), 79) )
/\  (bitv_binop_inner binop v v' 80 = SOME (w2v ((get_word_binop binop) ((v2w v): 80 word) ((v2w v'): 80 word)), 80) )
/\  (bitv_binop_inner binop v v' 81 = SOME (w2v ((get_word_binop binop) ((v2w v): 81 word) ((v2w v'): 81 word)), 81) )
/\  (bitv_binop_inner binop v v' 82 = SOME (w2v ((get_word_binop binop) ((v2w v): 82 word) ((v2w v'): 82 word)), 82) )
/\  (bitv_binop_inner binop v v' 83 = SOME (w2v ((get_word_binop binop) ((v2w v): 83 word) ((v2w v'): 83 word)), 83) )
/\  (bitv_binop_inner binop v v' 84 = SOME (w2v ((get_word_binop binop) ((v2w v): 84 word) ((v2w v'): 84 word)), 84) )
/\  (bitv_binop_inner binop v v' 85 = SOME (w2v ((get_word_binop binop) ((v2w v): 85 word) ((v2w v'): 85 word)), 85) )
/\  (bitv_binop_inner binop v v' 86 = SOME (w2v ((get_word_binop binop) ((v2w v): 86 word) ((v2w v'): 86 word)), 86) )
/\  (bitv_binop_inner binop v v' 87 = SOME (w2v ((get_word_binop binop) ((v2w v): 87 word) ((v2w v'): 87 word)), 87) )
/\  (bitv_binop_inner binop v v' 88 = SOME (w2v ((get_word_binop binop) ((v2w v): 88 word) ((v2w v'): 88 word)), 88) )
/\  (bitv_binop_inner binop v v' 89 = SOME (w2v ((get_word_binop binop) ((v2w v): 89 word) ((v2w v'): 89 word)), 89) )
/\  (bitv_binop_inner binop v v' 90 = SOME (w2v ((get_word_binop binop) ((v2w v): 90 word) ((v2w v'): 90 word)), 90) )
/\  (bitv_binop_inner binop v v' 91 = SOME (w2v ((get_word_binop binop) ((v2w v): 91 word) ((v2w v'): 91 word)), 91) )
/\  (bitv_binop_inner binop v v' 92 = SOME (w2v ((get_word_binop binop) ((v2w v): 92 word) ((v2w v'): 92 word)), 92) )
/\  (bitv_binop_inner binop v v' 93 = SOME (w2v ((get_word_binop binop) ((v2w v): 93 word) ((v2w v'): 93 word)), 93) )
/\  (bitv_binop_inner binop v v' 94 = SOME (w2v ((get_word_binop binop) ((v2w v): 94 word) ((v2w v'): 94 word)), 94) )
/\  (bitv_binop_inner binop v v' 95 = SOME (w2v ((get_word_binop binop) ((v2w v): 95 word) ((v2w v'): 95 word)), 95) )
/\  (bitv_binop_inner binop v v' 96 = SOME (w2v ((get_word_binop binop) ((v2w v): 96 word) ((v2w v'): 96 word)), 96) )
/\  (bitv_binop_inner binop v v' 97 = SOME (w2v ((get_word_binop binop) ((v2w v): 97 word) ((v2w v'): 97 word)), 97) )
/\  (bitv_binop_inner binop v v' 98 = SOME (w2v ((get_word_binop binop) ((v2w v): 98 word) ((v2w v'): 98 word)), 98) )
/\  (bitv_binop_inner binop v v' 99 = SOME (w2v ((get_word_binop binop) ((v2w v): 99 word) ((v2w v'): 99 word)), 99) )
/\  (bitv_binop_inner binop v v' 100 = SOME (w2v ((get_word_binop binop) ((v2w v): 100 word) ((v2w v'): 100 word)), 100) )
/\  (bitv_binop_inner binop v v' 101 = SOME (w2v ((get_word_binop binop) ((v2w v): 101 word) ((v2w v'): 101 word)), 101) )
/\  (bitv_binop_inner binop v v' 102 = SOME (w2v ((get_word_binop binop) ((v2w v): 102 word) ((v2w v'): 102 word)), 102) )
/\  (bitv_binop_inner binop v v' 103 = SOME (w2v ((get_word_binop binop) ((v2w v): 103 word) ((v2w v'): 103 word)), 103) )
/\  (bitv_binop_inner binop v v' 104 = SOME (w2v ((get_word_binop binop) ((v2w v): 104 word) ((v2w v'): 104 word)), 104) )
/\  (bitv_binop_inner binop v v' 105 = SOME (w2v ((get_word_binop binop) ((v2w v): 105 word) ((v2w v'): 105 word)), 105) )
/\  (bitv_binop_inner binop v v' 106 = SOME (w2v ((get_word_binop binop) ((v2w v): 106 word) ((v2w v'): 106 word)), 106) )
/\  (bitv_binop_inner binop v v' 107 = SOME (w2v ((get_word_binop binop) ((v2w v): 107 word) ((v2w v'): 107 word)), 107) )
/\  (bitv_binop_inner binop v v' 108 = SOME (w2v ((get_word_binop binop) ((v2w v): 108 word) ((v2w v'): 108 word)), 108) )
/\  (bitv_binop_inner binop v v' 109 = SOME (w2v ((get_word_binop binop) ((v2w v): 109 word) ((v2w v'): 109 word)), 109) )
/\  (bitv_binop_inner binop v v' 110 = SOME (w2v ((get_word_binop binop) ((v2w v): 110 word) ((v2w v'): 110 word)), 110) )
/\  (bitv_binop_inner binop v v' 111 = SOME (w2v ((get_word_binop binop) ((v2w v): 111 word) ((v2w v'): 111 word)), 111) )
/\  (bitv_binop_inner binop v v' 112 = SOME (w2v ((get_word_binop binop) ((v2w v): 112 word) ((v2w v'): 112 word)), 112) )
/\  (bitv_binop_inner binop v v' 113 = SOME (w2v ((get_word_binop binop) ((v2w v): 113 word) ((v2w v'): 113 word)), 113) )
/\  (bitv_binop_inner binop v v' 114 = SOME (w2v ((get_word_binop binop) ((v2w v): 114 word) ((v2w v'): 114 word)), 114) )
/\  (bitv_binop_inner binop v v' 115 = SOME (w2v ((get_word_binop binop) ((v2w v): 115 word) ((v2w v'): 115 word)), 115) )
/\  (bitv_binop_inner binop v v' 116 = SOME (w2v ((get_word_binop binop) ((v2w v): 116 word) ((v2w v'): 116 word)), 116) )
/\  (bitv_binop_inner binop v v' 117 = SOME (w2v ((get_word_binop binop) ((v2w v): 117 word) ((v2w v'): 117 word)), 117) )
/\  (bitv_binop_inner binop v v' 118 = SOME (w2v ((get_word_binop binop) ((v2w v): 118 word) ((v2w v'): 118 word)), 118) )
/\  (bitv_binop_inner binop v v' 119 = SOME (w2v ((get_word_binop binop) ((v2w v): 119 word) ((v2w v'): 119 word)), 119) )
/\  (bitv_binop_inner binop v v' 120 = SOME (w2v ((get_word_binop binop) ((v2w v): 120 word) ((v2w v'): 120 word)), 120) )
/\  (bitv_binop_inner binop v v' 121 = SOME (w2v ((get_word_binop binop) ((v2w v): 121 word) ((v2w v'): 121 word)), 121) )
/\  (bitv_binop_inner binop v v' 122 = SOME (w2v ((get_word_binop binop) ((v2w v): 122 word) ((v2w v'): 122 word)), 122) )
/\  (bitv_binop_inner binop v v' 123 = SOME (w2v ((get_word_binop binop) ((v2w v): 123 word) ((v2w v'): 123 word)), 123) )
/\  (bitv_binop_inner binop v v' 124 = SOME (w2v ((get_word_binop binop) ((v2w v): 124 word) ((v2w v'): 124 word)), 124) )
/\  (bitv_binop_inner binop v v' 125 = SOME (w2v ((get_word_binop binop) ((v2w v): 125 word) ((v2w v'): 125 word)), 125) )
/\  (bitv_binop_inner binop v v' 126 = SOME (w2v ((get_word_binop binop) ((v2w v): 126 word) ((v2w v'): 126 word)), 126) )
/\  (bitv_binop_inner binop v v' 127 = SOME (w2v ((get_word_binop binop) ((v2w v): 127 word) ((v2w v'): 127 word)), 127) )
/\  (bitv_binop_inner binop v v' 128 = SOME (w2v ((get_word_binop binop) ((v2w v): 128 word) ((v2w v'): 128 word)), 128) )
/\  (bitv_binop_inner binop v v' _ = NONE )
End

Definition bitv_binop_old_def:
  bitv_binop_old binop (v, n) (v', n') =
    if n = n'
    then bitv_binop_inner binop v v' n
    else NONE
End

Definition word_eq_def:
 (word_eq w1 w2 =
  AND_EL (MAP bit_eq (ZIP(w2v w1, w2v w2))))
End

Definition get_word_binpred_def:
    (get_word_binpred binop_le = word_ls)
/\  (get_word_binpred binop_ge = word_hs)
/\  (get_word_binpred binop_lt = word_lo)
/\  (get_word_binpred binop_gt = word_hi)
/\  (get_word_binpred binop_neq = (\w1 w2. ~(word_eq w1 w2)))
/\  (get_word_binpred binop_eq = (\w1 w2. word_eq w1 w2))
End

Definition bitv_binpred_inner_def:
    (bitv_binpred_inner binpred v v' (1:num) = SOME (((get_word_binpred binpred) ((v2w v): 1 word) ((v2w v'): 1 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 2 = SOME (((get_word_binpred binpred) ((v2w v): 2 word) ((v2w v'): 2 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 3 = SOME (((get_word_binpred binpred) ((v2w v): 3 word) ((v2w v'): 3 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 4 = SOME (((get_word_binpred binpred) ((v2w v): 4 word) ((v2w v'): 4 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 5 = SOME (((get_word_binpred binpred) ((v2w v): 5 word) ((v2w v'): 5 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 6 = SOME (((get_word_binpred binpred) ((v2w v): 6 word) ((v2w v'): 6 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 7 = SOME (((get_word_binpred binpred) ((v2w v): 7 word) ((v2w v'): 7 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 8 = SOME (((get_word_binpred binpred) ((v2w v): 8 word) ((v2w v'): 8 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 9 = SOME (((get_word_binpred binpred) ((v2w v): 9 word) ((v2w v'): 9 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 10 = SOME (((get_word_binpred binpred) ((v2w v): 10 word) ((v2w v'): 10 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 11 = SOME (((get_word_binpred binpred) ((v2w v): 11 word) ((v2w v'): 11 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 12 = SOME (((get_word_binpred binpred) ((v2w v): 12 word) ((v2w v'): 12 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 13 = SOME (((get_word_binpred binpred) ((v2w v): 13 word) ((v2w v'): 13 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 14 = SOME (((get_word_binpred binpred) ((v2w v): 14 word) ((v2w v'): 14 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 15 = SOME (((get_word_binpred binpred) ((v2w v): 15 word) ((v2w v'): 15 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 16 = SOME (((get_word_binpred binpred) ((v2w v): 16 word) ((v2w v'): 16 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 17 = SOME (((get_word_binpred binpred) ((v2w v): 17 word) ((v2w v'): 17 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 18 = SOME (((get_word_binpred binpred) ((v2w v): 18 word) ((v2w v'): 18 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 19 = SOME (((get_word_binpred binpred) ((v2w v): 19 word) ((v2w v'): 19 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 20 = SOME (((get_word_binpred binpred) ((v2w v): 20 word) ((v2w v'): 20 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 21 = SOME (((get_word_binpred binpred) ((v2w v): 21 word) ((v2w v'): 21 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 22 = SOME (((get_word_binpred binpred) ((v2w v): 22 word) ((v2w v'): 22 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 23 = SOME (((get_word_binpred binpred) ((v2w v): 23 word) ((v2w v'): 23 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 24 = SOME (((get_word_binpred binpred) ((v2w v): 24 word) ((v2w v'): 24 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 25 = SOME (((get_word_binpred binpred) ((v2w v): 25 word) ((v2w v'): 25 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 26 = SOME (((get_word_binpred binpred) ((v2w v): 26 word) ((v2w v'): 26 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 27 = SOME (((get_word_binpred binpred) ((v2w v): 27 word) ((v2w v'): 27 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 28 = SOME (((get_word_binpred binpred) ((v2w v): 28 word) ((v2w v'): 28 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 29 = SOME (((get_word_binpred binpred) ((v2w v): 29 word) ((v2w v'): 29 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 30 = SOME (((get_word_binpred binpred) ((v2w v): 30 word) ((v2w v'): 30 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 31 = SOME (((get_word_binpred binpred) ((v2w v): 31 word) ((v2w v'): 31 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 32 = SOME (((get_word_binpred binpred) ((v2w v): 32 word) ((v2w v'): 32 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 33 = SOME (((get_word_binpred binpred) ((v2w v): 33 word) ((v2w v'): 33 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 34 = SOME (((get_word_binpred binpred) ((v2w v): 34 word) ((v2w v'): 34 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 35 = SOME (((get_word_binpred binpred) ((v2w v): 35 word) ((v2w v'): 35 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 36 = SOME (((get_word_binpred binpred) ((v2w v): 36 word) ((v2w v'): 36 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 37 = SOME (((get_word_binpred binpred) ((v2w v): 37 word) ((v2w v'): 37 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 38 = SOME (((get_word_binpred binpred) ((v2w v): 38 word) ((v2w v'): 38 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 39 = SOME (((get_word_binpred binpred) ((v2w v): 39 word) ((v2w v'): 39 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 40 = SOME (((get_word_binpred binpred) ((v2w v): 40 word) ((v2w v'): 40 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 41 = SOME (((get_word_binpred binpred) ((v2w v): 41 word) ((v2w v'): 41 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 42 = SOME (((get_word_binpred binpred) ((v2w v): 42 word) ((v2w v'): 42 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 43 = SOME (((get_word_binpred binpred) ((v2w v): 43 word) ((v2w v'): 43 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 44 = SOME (((get_word_binpred binpred) ((v2w v): 44 word) ((v2w v'): 44 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 45 = SOME (((get_word_binpred binpred) ((v2w v): 45 word) ((v2w v'): 45 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 46 = SOME (((get_word_binpred binpred) ((v2w v): 46 word) ((v2w v'): 46 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 47 = SOME (((get_word_binpred binpred) ((v2w v): 47 word) ((v2w v'): 47 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 48 = SOME (((get_word_binpred binpred) ((v2w v): 48 word) ((v2w v'): 48 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 49 = SOME (((get_word_binpred binpred) ((v2w v): 49 word) ((v2w v'): 49 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 50 = SOME (((get_word_binpred binpred) ((v2w v): 50 word) ((v2w v'): 50 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 51 = SOME (((get_word_binpred binpred) ((v2w v): 51 word) ((v2w v'): 51 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 52 = SOME (((get_word_binpred binpred) ((v2w v): 52 word) ((v2w v'): 52 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 53 = SOME (((get_word_binpred binpred) ((v2w v): 53 word) ((v2w v'): 53 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 54 = SOME (((get_word_binpred binpred) ((v2w v): 54 word) ((v2w v'): 54 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 55 = SOME (((get_word_binpred binpred) ((v2w v): 55 word) ((v2w v'): 55 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 56 = SOME (((get_word_binpred binpred) ((v2w v): 56 word) ((v2w v'): 56 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 57 = SOME (((get_word_binpred binpred) ((v2w v): 57 word) ((v2w v'): 57 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 58 = SOME (((get_word_binpred binpred) ((v2w v): 58 word) ((v2w v'): 58 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 59 = SOME (((get_word_binpred binpred) ((v2w v): 59 word) ((v2w v'): 59 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 60 = SOME (((get_word_binpred binpred) ((v2w v): 60 word) ((v2w v'): 60 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 61 = SOME (((get_word_binpred binpred) ((v2w v): 61 word) ((v2w v'): 61 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 62 = SOME (((get_word_binpred binpred) ((v2w v): 62 word) ((v2w v'): 62 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 63 = SOME (((get_word_binpred binpred) ((v2w v): 63 word) ((v2w v'): 63 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 64 = SOME (((get_word_binpred binpred) ((v2w v): 64 word) ((v2w v'): 64 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 65 = SOME (((get_word_binpred binpred) ((v2w v): 65 word) ((v2w v'): 65 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 66 = SOME (((get_word_binpred binpred) ((v2w v): 66 word) ((v2w v'): 66 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 67 = SOME (((get_word_binpred binpred) ((v2w v): 67 word) ((v2w v'): 67 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 68 = SOME (((get_word_binpred binpred) ((v2w v): 68 word) ((v2w v'): 68 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 69 = SOME (((get_word_binpred binpred) ((v2w v): 69 word) ((v2w v'): 69 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 70 = SOME (((get_word_binpred binpred) ((v2w v): 70 word) ((v2w v'): 70 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 71 = SOME (((get_word_binpred binpred) ((v2w v): 71 word) ((v2w v'): 71 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 72 = SOME (((get_word_binpred binpred) ((v2w v): 72 word) ((v2w v'): 72 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 73 = SOME (((get_word_binpred binpred) ((v2w v): 73 word) ((v2w v'): 73 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 74 = SOME (((get_word_binpred binpred) ((v2w v): 74 word) ((v2w v'): 74 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 75 = SOME (((get_word_binpred binpred) ((v2w v): 75 word) ((v2w v'): 75 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 76 = SOME (((get_word_binpred binpred) ((v2w v): 76 word) ((v2w v'): 76 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 77 = SOME (((get_word_binpred binpred) ((v2w v): 77 word) ((v2w v'): 77 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 78 = SOME (((get_word_binpred binpred) ((v2w v): 78 word) ((v2w v'): 78 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 79 = SOME (((get_word_binpred binpred) ((v2w v): 79 word) ((v2w v'): 79 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 80 = SOME (((get_word_binpred binpred) ((v2w v): 80 word) ((v2w v'): 80 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 81 = SOME (((get_word_binpred binpred) ((v2w v): 81 word) ((v2w v'): 81 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 82 = SOME (((get_word_binpred binpred) ((v2w v): 82 word) ((v2w v'): 82 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 83 = SOME (((get_word_binpred binpred) ((v2w v): 83 word) ((v2w v'): 83 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 84 = SOME (((get_word_binpred binpred) ((v2w v): 84 word) ((v2w v'): 84 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 85 = SOME (((get_word_binpred binpred) ((v2w v): 85 word) ((v2w v'): 85 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 86 = SOME (((get_word_binpred binpred) ((v2w v): 86 word) ((v2w v'): 86 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 87 = SOME (((get_word_binpred binpred) ((v2w v): 87 word) ((v2w v'): 87 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 88 = SOME (((get_word_binpred binpred) ((v2w v): 88 word) ((v2w v'): 88 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 89 = SOME (((get_word_binpred binpred) ((v2w v): 89 word) ((v2w v'): 89 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 90 = SOME (((get_word_binpred binpred) ((v2w v): 90 word) ((v2w v'): 90 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 91 = SOME (((get_word_binpred binpred) ((v2w v): 91 word) ((v2w v'): 91 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 92 = SOME (((get_word_binpred binpred) ((v2w v): 92 word) ((v2w v'): 92 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 93 = SOME (((get_word_binpred binpred) ((v2w v): 93 word) ((v2w v'): 93 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 94 = SOME (((get_word_binpred binpred) ((v2w v): 94 word) ((v2w v'): 94 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 95 = SOME (((get_word_binpred binpred) ((v2w v): 95 word) ((v2w v'): 95 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 96 = SOME (((get_word_binpred binpred) ((v2w v): 96 word) ((v2w v'): 96 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 97 = SOME (((get_word_binpred binpred) ((v2w v): 97 word) ((v2w v'): 97 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 98 = SOME (((get_word_binpred binpred) ((v2w v): 98 word) ((v2w v'): 98 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 99 = SOME (((get_word_binpred binpred) ((v2w v): 99 word) ((v2w v'): 99 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 100 = SOME (((get_word_binpred binpred) ((v2w v): 100 word) ((v2w v'): 100 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 101 = SOME (((get_word_binpred binpred) ((v2w v): 101 word) ((v2w v'): 101 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 102 = SOME (((get_word_binpred binpred) ((v2w v): 102 word) ((v2w v'): 102 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 103 = SOME (((get_word_binpred binpred) ((v2w v): 103 word) ((v2w v'): 103 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 104 = SOME (((get_word_binpred binpred) ((v2w v): 104 word) ((v2w v'): 104 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 105 = SOME (((get_word_binpred binpred) ((v2w v): 105 word) ((v2w v'): 105 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 106 = SOME (((get_word_binpred binpred) ((v2w v): 106 word) ((v2w v'): 106 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 107 = SOME (((get_word_binpred binpred) ((v2w v): 107 word) ((v2w v'): 107 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 108 = SOME (((get_word_binpred binpred) ((v2w v): 108 word) ((v2w v'): 108 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 109 = SOME (((get_word_binpred binpred) ((v2w v): 109 word) ((v2w v'): 109 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 110 = SOME (((get_word_binpred binpred) ((v2w v): 110 word) ((v2w v'): 110 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 111 = SOME (((get_word_binpred binpred) ((v2w v): 111 word) ((v2w v'): 111 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 112 = SOME (((get_word_binpred binpred) ((v2w v): 112 word) ((v2w v'): 112 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 113 = SOME (((get_word_binpred binpred) ((v2w v): 113 word) ((v2w v'): 113 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 114 = SOME (((get_word_binpred binpred) ((v2w v): 114 word) ((v2w v'): 114 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 115 = SOME (((get_word_binpred binpred) ((v2w v): 115 word) ((v2w v'): 115 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 116 = SOME (((get_word_binpred binpred) ((v2w v): 116 word) ((v2w v'): 116 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 117 = SOME (((get_word_binpred binpred) ((v2w v): 117 word) ((v2w v'): 117 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 118 = SOME (((get_word_binpred binpred) ((v2w v): 118 word) ((v2w v'): 118 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 119 = SOME (((get_word_binpred binpred) ((v2w v): 119 word) ((v2w v'): 119 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 120 = SOME (((get_word_binpred binpred) ((v2w v): 120 word) ((v2w v'): 120 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 121 = SOME (((get_word_binpred binpred) ((v2w v): 121 word) ((v2w v'): 121 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 122 = SOME (((get_word_binpred binpred) ((v2w v): 122 word) ((v2w v'): 122 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 123 = SOME (((get_word_binpred binpred) ((v2w v): 123 word) ((v2w v'): 123 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 124 = SOME (((get_word_binpred binpred) ((v2w v): 124 word) ((v2w v'): 124 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 125 = SOME (((get_word_binpred binpred) ((v2w v): 125 word) ((v2w v'): 125 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 126 = SOME (((get_word_binpred binpred) ((v2w v): 126 word) ((v2w v'): 126 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 127 = SOME (((get_word_binpred binpred) ((v2w v): 127 word) ((v2w v'): 127 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' 128 = SOME (((get_word_binpred binpred) ((v2w v): 128 word) ((v2w v'): 128 word)):boolv) )
/\  (bitv_binpred_inner binpred v v' _ = NONE )
End
Definition bitv_binpred_old_def:
  bitv_binpred_old binpred (v, n) (v', n') =
    if n = n'
    then bitv_binpred_inner binpred v v' n
    else NONE
End


(* TODO: Don't hard-code "r" *)
fun brute_unop_arithmetic_tac (width:int) =
 let
  val list_tm = “q:bool list”
  val dim = fcpLib.index_type $ Arbnum.fromInt width
  val dimword_tm = mk_eq (wordsSyntax.mk_dimword dim, numSyntax.mk_exp (numSyntax.term_of_int 2, numSyntax.term_of_int width))
  val sub_tm = numSyntax.mk_minus (wordsSyntax.mk_dimword dim, numSyntax.mk_mod (bitstringSyntax.mk_v2n list_tm, wordsSyntax.mk_dimword dim))
 in
  tmCases_on (mk_eq(mk_var("r", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   rpt (qpat_x_assum ‘r ≠ _’ (fn thm => ALL_TAC)) >>
   rpt strip_tac >- (
    assume_tac $ SPEC list_tm bitstringTheory.v2n_lt >>
    gs[]
   ) >>
   ASM_REWRITE_TAC[bitv_unop_old_def, get_word_unop_def] >>
   blastLib.BBLAST_TAC >>
   gs[bitstringTheory.ops_to_n2w] >>
   assume_tac $ INST_TYPE [alpha |-> dim] $ SPEC sub_tm wordsTheory.n2w_mod >>
   (* TODO: Find a better way to do this? *)
   SUBGOAL_THEN dimword_tm STRIP_ASSUME_TAC >- (gs[]) >>
   FULL_SIMP_TAC std_ss [] >>
   gs[] >>
   assume_tac $ SPEC sub_tm $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   gs[] >>
   assume_tac $ SPEC list_tm bitstringTheory.v2n_lt >>
   gvs[]
  )
 end
;

(* This is very slow for the most trivial cases (un_plus), this could be specialised *)
fun brute_unop_arithmetic_tac' (width:int) =
 let
(*
 val width = 8
*)
  val list_tm = “bl:bool list”
  val dim = fcpLib.index_type $ Arbnum.fromInt width
  val dimword_tm = mk_eq (wordsSyntax.mk_dimword dim, numSyntax.mk_exp (numSyntax.term_of_int 2, numSyntax.term_of_int width))
  val sub_tm = numSyntax.mk_minus (wordsSyntax.mk_dimword dim, numSyntax.mk_mod (bitstringSyntax.mk_v2n list_tm, wordsSyntax.mk_dimword dim))
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
(* OK for un_plus *)
(*
   rpt (qpat_x_assum ‘n ≠ _’ (fn thm => ALL_TAC)) >>
   gvs[bitv_unop_old_def, unop_exec_def, get_word_unop_def] >>
   gs[bitstringTheory.w2v_v2w]
*)
(* OK for neg_signed *)
(*
   rpt (qpat_x_assum ‘n ≠ _’ (fn thm => ALL_TAC)) >>
   FULL_SIMP_TAC std_ss [bitv_unop_old_def, unop_exec_def, get_word_unop_def, bitv_2comp_def, bitv_1comp_def] >>
   rw[bitstringTheory.ops_to_n2w] >>

   assume_tac $ INST_TYPE [alpha |-> dim] $ SPEC sub_tm wordsTheory.n2w_mod >>
   (* TODO: Better way to do this??? *)
   SUBGOAL_THEN dimword_tm STRIP_ASSUME_TAC >- (gs[]) >>
   FULL_SIMP_TAC std_ss [] >>
   gs[] >>
   assume_tac $ SPEC sub_tm $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   gs[] >>
   assume_tac $ SPEC list_tm bitstringTheory.v2n_lt >>
   gvs[] >>
   gs[bitstringTheory.w2v_v2w]
*)
   rpt (qpat_x_assum ‘n ≠ _’ (fn thm => ALL_TAC)) >>
   FULL_SIMP_TAC std_ss [bitv_unop_old_def, unop_exec_def, bitv_unop_def, get_word_unop_def, bitv_2comp_def, bitv_1comp_def, bitstringTheory.word_1comp_v2w, bitstringTheory.bnot_def] >>
   rw[bitstringTheory.ops_to_n2w] >>

   assume_tac $ INST_TYPE [alpha |-> dim] $ SPEC sub_tm wordsTheory.n2w_mod >>
   (* TODO: Better way to do this??? *)
   SUBGOAL_THEN dimword_tm STRIP_ASSUME_TAC >- (gs[]) >>
   FULL_SIMP_TAC std_ss [] >>
   gs[] >>
   assume_tac $ SPEC sub_tm $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   gs[] >>
   assume_tac $ SPEC list_tm bitstringTheory.v2n_lt >>
   gvs[] >>
   gs[bitstringTheory.w2v_v2w]
  )
 end
;

fun rpt_interval_tac desc min max tac =
 let
  val widths = upto min max
  val tacs = map (fn width => tac width) widths
  val _ = print ("Proving arithmetic equivalence: "^desc^"...\n")
 in
  foldr (op THEN) ALL_TAC tacs
 end
;

Theorem greater_suc:
!(n:num) m.
n > m /\ n ≠ (m + 1) ==> n > (m + 1)
Proof
decide_tac
QED

Theorem less_eq_greater:
!(n:num) m.
n <= m /\ n > m ==> F
Proof
decide_tac
QED

(* TODO: Very similar to arithmeticTheory.NOT_ZERO *)
Theorem not_zero_greater:
!(n:num).
n <> 0 ==> n > 0
Proof
decide_tac
QED

(* TODO: Unify with brute_arithmetic_finish_tac *)
fun brute_unop_arithmetic_finish_tac min max =
 let
  val widths = upto min max
  val tacs = map (fn width => imp_res_tac $ REWRITE_RULE [SIMP_CONV arith_ss [] (numSyntax.mk_plus(numSyntax.term_of_int width, “1:num”))] $ SPECL [“n:num”, numSyntax.term_of_int width] greater_suc) widths
 in
  (foldr (op THEN) ALL_TAC tacs) >>
  imp_res_tac less_eq_greater
 end
;

(********************)
(* Unary operations *)
(********************)

(* e_neg_bool *)
Theorem unop_neg_correct:
!b b'.
~b = b' ==>
unop_exec unop_neg (v_bool b) = SOME (v_bool b')
Proof
rpt strip_tac >>
gs[unop_exec_def]
QED

(* e_compl *)
Theorem unop_compl_correct:
!bl n bl' n'.
n > 0 ==>
n <= 128 ==>
LENGTH bl = n ==>
bitv_bl_unop bnot (bl,n) = (bl',n') ==>
unop_exec unop_compl (v_bit (bl,n)) = SOME (v_bit (bl',n'))
Proof
rpt strip_tac >>
gs[bitv_bl_unop_def, unop_exec_def, bitv_unop_def, bitv_1comp_def, bitstringTheory.bnot_def]
QED

(* Old, using bitv_unop_old from the regular semantics
Theorem unop_compl_correct:
!bl n bl' n'.
n > 0 ==>
n <= 128 ==>
LENGTH bl = n ==>
bitv_unop_old unop_compl (bl,n) = (bl',n') ==>
unop_exec unop_compl (v_bit (bl,n)) = SOME (v_bit (bl',n'))
Proof
rpt strip_tac >>
rpt_interval_tac "complement" 1 128 brute_unop_arithmetic_tac' >>
brute_unop_arithmetic_finish_tac 0 128
QED

Theorem unop_un_plus_correct:
!bl n bl' n'.
n > 0 ==>
n <= 128 ==>
LENGTH bl = n ==>
bitv_unop_old unop_un_plus (bl,n) = (bl',n') ==>
unop_exec unop_un_plus (v_bit (bl,n)) = SOME (v_bit (bl',n'))
Proof
rpt strip_tac >>
rpt_interval_tac "unary plus" 1 128 brute_unop_arithmetic_tac' >>
brute_unop_arithmetic_finish_tac 0 128
QED
*)

(* e_neg_signed *)
(* Relates
w2v (word_2comp (v2w v))

to

fixwidth (LENGTH v) (n2v ((2 ** LENGTH v) − (v2n v))))
*)
Theorem unop_neg_signed_correct:
!bl n bl' n'.
n > 0 ==>
n <= 128 ==>
LENGTH bl = n ==>
bitv_unop_old unop_neg_signed (bl,n) = (bl',n') ==>
unop_exec unop_neg_signed (v_bit (bl,n)) = SOME (v_bit (bl',n'))
Proof
rpt strip_tac >>
rpt_interval_tac "signed negation" 1 128 brute_unop_arithmetic_tac' >>
brute_unop_arithmetic_finish_tac 0 128
QED

(* e_un_plus *)
Theorem unop_un_plus_correct:
!bl n bl' n'.
n > 0 ==>
n <= 128 ==>
LENGTH bl = n ==>
(bl,n) = (bl',n') ==>
unop_exec unop_un_plus (v_bit (bl,n)) = SOME (v_bit (bl',n'))
Proof
rpt strip_tac >>
gs[unop_exec_def]
QED

(*********************)
(* Binary operations *)
(*********************)

(* TODO: Don't hard-code "n" *)
fun brute_addition_tac (width:int) =
 let
(*
val width = 8
val desc = "test"
*)
  val desc = "addition"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   ‘LENGTH bl = ^width_tm’ by gs[] >>
   gvs[bitv_binop_inner_def, bitv_binpred_inner_def, bitv_bl_binop_def, bitv_add_def, wordsTheory.saturate_add_def, bitv_mod_def, wordsTheory.saturate_sub_def, get_word_binop_def, get_word_binpred_def, wordsTheory.word_lsl_bv_def, wordsTheory.word_lsr_bv_def] >>
   gs[bitstringTheory.ops_to_n2w, wordsTheory.n2w_w2n, bitstringTheory.word_lsl_v2w, bitstringTheory.w2v_v2w, bitstringTheory.word_lsr_v2w] >>
   gs[wordsTheory.word_add_n2w] >>
   gs[binop_exec_def, bitv_bl_binop_def, bitv_binop_def, bitv_binpred_def, get_bitv_binop_def, get_bitv_binpred_def, bitv_add_def, bitv_saturate_add_def, bitv_saturate_sub_def, AllCaseEqs()] >>
   qpat_x_assum ‘LENGTH bl = ^width_tm’ (fn thm => gs[thm]) >>
   REWRITE_TAC[SIMP_RULE (srw_ss()) [] $ GSYM $ INST_TYPE [alpha |-> dim] bitstringTheory.w2v_v2w] >>
   gs[]
  ) >>
  (* All except last *)
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

(*
val min = 1
val max = 1
*)
fun brute_arithmetic_tac tac min max =
 let
  val widths = upto min max
  val tacs = map tac widths
 in
  foldr (op THEN) ALL_TAC tacs
 end
;

(*
val width = 65

val max = 128
val min = 65
val bitvs = ["bl", "bl1", "bl2"]
brute_arithmetic_tac 65 128 ["bl", "bl1", "bl2"]
*)

fun brute_arithmetic_finish_tac min max =
 let
  val widths = upto min max
  val tacs = map (fn width => imp_res_tac $ REWRITE_RULE [SIMP_CONV arith_ss [] (numSyntax.mk_plus(numSyntax.term_of_int width, “1:num”))] $ SPECL [“n:num”, numSyntax.term_of_int width] greater_suc) widths
 in
  (foldr (op THEN) ALL_TAC tacs) >>
  imp_res_tac less_eq_greater
 end
;

Theorem bitv_binop_inner:
!q q' r binop bitv3.
bitv_binop_inner binop q q' r = SOME bitv3 ==>
r <= 128 /\ r > 0
Proof
rpt strip_tac >>
(* Note the below is very delicate due to the number of subgoals and assumptions *)
FULL_SIMP_TAC std_ss [bitv_binop_inner_def] >>
FULL_SIMP_TAC bool_ss [AllCaseEqs()] >> (
 SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC bool_ss [optionTheory.NOT_NONE_SOME]
QED

Theorem bitv_binpred_inner:
!q q' r binop b.
bitv_binpred_inner binop q q' r = SOME b ==>
r <= 128 /\ r > 0
Proof
rpt strip_tac >>
(* Note the below is very delicate due to the number of subgoals and assumptions *)
FULL_SIMP_TAC std_ss [bitv_binpred_inner_def] >>
FULL_SIMP_TAC bool_ss [AllCaseEqs()] >> (
 SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC bool_ss [optionTheory.NOT_NONE_SOME]
QED

fun brute_multiplication_tac (width:int) =
 let
(*
val width = 8
*)
  val desc = "multiplication"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (   
   gvs[bitv_binop_inner_def, bitv_mul_def, get_word_binop_def] >>
   gs[bitstringTheory.ops_to_n2w] >>
   gs[wordsTheory.word_mul_n2w] >>
   assume_tac $ SPEC “(v2n bl * v2n bl')” $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   Cases_on ‘v2n bl * v2n bl' <= 2 ** ^width_tm’ >- (
    gs[wordsTheory.word_mul_n2w]
   ) >>
   gs[bitstringTheory.n2w_v2n, wordsTheory.word_mul_def, bitstringTheory.w2n_v2w, bitTheory.MOD_2EXP_def] >>
   ‘v2n bl < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl:bool list” bitstringTheory.v2n_lt >> gs[]) >>
   ‘v2n bl' < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl':bool list” bitstringTheory.v2n_lt >> gs[]) >>
   gs[SIMP_RULE (srw_ss()) [] $ SPEC “n2v (v2n bl * v2n bl')” $ INST_TYPE [alpha |-> dim] $ GSYM bitstringTheory.w2v_v2w]
  ) >>
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

Theorem binop_mul_correct:
!bl bl' n bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_inner binop_mul bl bl' n = SOME (bl'', n'') ==>
bitv_mul bl bl' n = bl''
Proof
rpt strip_tac >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_multiplication_tac 1 128 >>
gs[]
QED

Theorem less_eq_div_mono:
!(a:num) b x. 0 < b /\ a <= x ==> a DIV b <= x
Proof
rpt strip_tac >>
assume_tac $ Q.SPECL [‘b’, ‘a’, ‘x*b’] arithmeticTheory.DIV_LE_MONOTONE >>
gs[arithmeticTheory.MULT_TO_DIV] >>
assume_tac $ Q.SPECL [‘1’, ‘a’, ‘b’, ‘x’] arithmeticTheory.LESS_MONO_MULT2 >>
gs[]
QED

fun brute_division_tac (width:int) =
 let
(*
val width = 8
*)
  val desc = "division"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   gvs[bitv_binop_inner_def, bitv_div_def, get_word_binop_def] >>
   gs[bitstringTheory.ops_to_n2w] >>
   gs[wordsTheory.word_div_def] >>
   assume_tac $ SPEC “(v2n bl DIV v2n bl')” $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   Cases_on ‘v2n bl DIV v2n bl' <= 2 ** ^width_tm’ >- (
    Cases_on ‘v2n bl' = 0’ >- (
     gs[]
    ) >>
    ‘v2n bl < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl:bool list” bitstringTheory.v2n_lt >> gs[]) >>
    ‘v2n bl' < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl':bool list” bitstringTheory.v2n_lt >> gs[]) >>
    assume_tac $ SPECL [“v2n bl”, “v2n bl'”, “(2:num) ** ^width_tm”] less_eq_div_mono >>
    gs[]
   ) >>
   gs[] >>
   Cases_on ‘v2n bl' <> 0’ >> (gs[]) >>
   ‘v2n bl < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl:bool list” bitstringTheory.v2n_lt >> gs[]) >>
   ‘v2n bl' < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl':bool list” bitstringTheory.v2n_lt >> gs[]) >>
   gs[SIMP_RULE (srw_ss()) [] $ SPEC “n2v (v2n bl DIV v2n bl')” $ INST_TYPE [alpha |-> dim] $ GSYM bitstringTheory.w2v_v2w]
  ) >>
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

Theorem binop_div_correct:
!bl bl' n bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_inner binop_div bl bl' n = SOME (bl'', n'') ==>
bitv_div bl bl' n = bl''
Proof
rpt strip_tac >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_division_tac 1 128 >>
gs[]
QED

fun brute_modulus_tac (width:int) =
 let
(*
val width = 8
*)
  val desc = "modulus"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (   
   gvs[bitv_binop_inner_def, get_word_binop_def, wordsTheory.word_mod_def] >>
   gs[bitstringTheory.ops_to_n2w] >>
   gs[binop_exec_def, bitv_binop_def, get_bitv_binop_def, (* bitv_binop'_def, get_bitv_binop'_def, *) bitv_mod_def, AllCaseEqs()] >>
   Cases_on ‘v2n bl' = 0’ >- (
    let
     val w2n_tm = (hurdUtils.inst_ty [alpha |-> dim] “w2n”)
    in
     ‘^w2n_tm (v2w bl') = 0’ by (
      gs[Once $ GSYM bitstringTheory.n2w_v2n]
     )
    end >>
    ASM_REWRITE_TAC[] >>
    gs[bitstringTheory.w2v_v2w]
   ) >>
   gs[bitstringTheory.w2n_v2w, bitTheory.MOD_2EXP_def] >>
   ‘(v2n bl MOD 2 ** LENGTH bl MOD (v2n bl' MOD 2 ** LENGTH bl)) = (v2n bl MOD v2n bl')’ suffices_by (
    strip_tac >>
    gs[] >>
    assume_tac $ SPEC “(v2n bl MOD v2n bl')” $ GSYM $ INST_TYPE [alpha |-> dim] $ GSYM w2v_n2w >>
    gs[] >>
    ‘v2n bl MOD v2n bl' <= 2 ** ^width_tm’ suffices_by (
     strip_tac >>
     gs[]
    ) >>
    gs[] >>
    ‘v2n bl' < 2 ** ^width_tm’ suffices_by (
     strip_tac >>
     assume_tac $ SPECL [“v2n bl'”, “v2n bl”] $ GEN_ALL arithmeticTheory.MOD_LESS_EQ >>
     assume_tac $ SPEC “(bl:bool list)” bitstringTheory.v2n_lt >>
     rfs[]
    ) >>
    assume_tac $ SPEC “(bl':bool list)” bitstringTheory.v2n_lt >>
    rfs[]
   ) >>
   fs[] >>
   ‘v2n bl MOD 2 ** ^width_tm = v2n bl /\ v2n bl' MOD 2 ** ^width_tm = v2n bl'’ suffices_by (
    gs[]
   ) >>
   CONJ_TAC >- (
    irule arithmeticTheory.LESS_MOD >>
    assume_tac $ SPEC “bl:bool list” bitstringTheory.v2n_lt >>
    gs[]
   ) >>
   irule arithmeticTheory.LESS_MOD >>
   assume_tac $ SPEC “bl':bool list” bitstringTheory.v2n_lt >>
   rfs[]
  ) >>
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

(* e_mod *)
Theorem binop_mod_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_old binop_mod (bl,n) (bl',n') = SOME (bl'',n'') ==>
binop_exec binop_mod (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def] >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_modulus_tac 1 128 >>
gs[]
QED

(* TODO: Integrate into brute_addition_tac *)
fun prove_binop_add_correct_inner width =
 let
  val width_tm = numSyntax.term_of_int width
  val width_num = Arbnum.fromInt width
  val dim = fcpLib.index_type width_num
 in
  prove(“!bl bl'. fixwidth ^width_tm (n2v (v2n bl + v2n bl')) = w2v (^(wordsSyntax.mk_n2w(“(v2n bl + v2n bl')”, dim)))”,
   gvs[bitv_binop_inner_def, bitv_binpred_inner_def, bitv_bl_binop_def, bitv_add_def, get_word_binop_def] >>
   gs[bitstringTheory.ops_to_n2w, wordsTheory.n2w_w2n, bitstringTheory.w2v_v2w] >>
   gs[wordsTheory.word_add_n2w] >>
   gs[binop_exec_def, bitv_bl_binop_def, bitv_binop_def, get_bitv_binop_def, bitv_add_def, AllCaseEqs()] >>
   REWRITE_TAC[SIMP_RULE (srw_ss()) [] $ GSYM $ INST_TYPE [alpha |-> dim] bitstringTheory.w2v_v2w] >>
   gs[]
  )
 end
;

(* e_add *)
(* Relates
fixwidth l (n2v (v2n a + v2n b))
to
(v2w a) + (v2w b)
*)
Theorem binop_add_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
bitv_binop_old binop_add (bl,n) (bl',n') = SOME (bl'',n'') ==>
binop_exec binop_add (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def] >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_addition_tac 1 128 >>
gs[]
QED

fun test_subtraction width n1 n2 =
 let
(*
 val n1 = 8
 val n2 = 7
 val width = 8
*)
  val n1_tm = numSyntax.term_of_int n1
  val n2_tm = numSyntax.term_of_int n2
  val width_tm = numSyntax.term_of_int width
  val res1 = EVAL “bitv_binop_old binop_sub (fixwidth ^width_tm $ n2v ^n1_tm, ^width_tm) (fixwidth ^width_tm $ n2v ^n2_tm, ^width_tm)”
  val res2 = EVAL “binop_exec binop_sub (v_bit (fixwidth ^width_tm $ n2v ^n1_tm, ^width_tm)) (v_bit (fixwidth ^width_tm $ n2v ^n2_tm, ^width_tm))”

  val res1_num = numSyntax.int_of_term $ rhs $ concl $ EVAL $bitstringSyntax.mk_v2n $ fst $ pairSyntax.dest_pair $ optionSyntax.dest_some $ rhs $ concl res1
  val res2_num = numSyntax.int_of_term $ rhs $ concl $ EVAL $bitstringSyntax.mk_v2n $ fst $ pairSyntax.dest_pair $ p4Syntax.dest_v_bit $ optionSyntax.dest_some $ rhs $ concl res2
 in
  print ("Result in old arithmetic: "^(Int.toString res1_num)^"\n");
  print ("Result in new arithmetic: "^(Int.toString res2_num)^"\n")
 end
;
(*
test_subtraction 8 8 7

test_subtraction 8 8 8

test_subtraction 8 130 1
*)

(* TODO: Don't hard-code "n" *)
fun brute_saturated_addition_tac (width:int) =
 let
(*
val width = 8
*)
  val desc = "saturated addition"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
  val w2n_tm = (hurdUtils.inst_ty [alpha |-> dim] “w2n”)
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   gvs[] >>
   gvs[bitv_binop_inner_def, get_word_binop_def, wordsTheory.saturate_add_def, wordsTheory.saturate_n2w_def] >>
   gs[bitstringTheory.ops_to_n2w, binop_exec_def, bitv_binop_def, get_bitv_binop_def, bitv_saturate_add_def, AllCaseEqs()] >>
   simp[EVAL “v2n $ REPLICATE ^width_tm T”] >>
   
   Cases_on ‘2 ** ^width_tm ≤ v2n bl + v2n bl'’ >> (gs[]) >- (
    assume_tac $ SPEC “((2:num) ** ^width_tm) - 1” $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
    gs[] >>
    qpat_x_assum ‘_ = fixwidth ^width_tm _’
     (fn thm => REWRITE_TAC [GSYM thm]) >>
    ‘2 ** ^width_tm ≤ (^w2n_tm) (v2w bl) + (^w2n_tm) (v2w bl')’ by (
     gs[rich_listTheory.REPLICATE_GENLIST] >>
     ‘v2n (REPLICATE ^width_tm T) = (2 ** ^width_tm) - 1’ by (
      gs[rich_listTheory.REPLICATE_GENLIST, bitstringTheory.v2n_def, bitstringTheory.bitify_def] >>
      qpat_x_assum ‘^width_tm = LENGTH bl'’ (fn thm => gs[GSYM thm])
     ) >>
     gs[rich_listTheory.REPLICATE_GENLIST] >>
     ‘v2n bl < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl:bool list” bitstringTheory.v2n_lt >> gs[]) >>
     ‘v2n bl' < 2 ** ^width_tm’ by (assume_tac $ SPEC “bl':bool list” bitstringTheory.v2n_lt >> gs[]) >>
     gs[bitstringTheory.w2n_v2w, bitTheory.MOD_2EXP_def]
    ) >>
    fs[bitstringTheory.w2v_def]
   ) >>
   assume_tac $ SPEC “(v2n bl + v2n bl')” $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   ‘v2n bl + v2n bl' < 2 ** ^width_tm’ by (
    gs[arithmeticTheory.NOT_LE, rich_listTheory.REPLICATE_GENLIST, bitstringTheory.v2n_def, bitstringTheory.bitify_def]
   ) >>
   gs[] >>
   qpat_x_assum ‘w2v (n2w (v2n bl + v2n bl')) = fixwidth ^width_tm (n2v (v2n bl + v2n bl'))’
    (fn thm => REWRITE_TAC [GSYM thm]) >>
   ‘2 ** ^width_tm > ^w2n_tm (v2w bl) + ^w2n_tm (v2w bl')’ by (
    gs[bitstringTheory.w2n_v2w, bitTheory.MOD_2EXP_def]
   ) >>
   gs[bitstringTheory.w2n_v2w, bitTheory.MOD_2EXP_def]
  ) >>
  (* All except last *)
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

(* This takes 930s to prove... *)
Theorem binop_sat_add_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_old binop_sat_add (bl,n) (bl',n') = SOME (bl'',n'') ==>
binop_exec binop_sat_add (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def] >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_saturated_addition_tac 1 128 >>
gs[]
QED

Theorem sub_lemma:
!n width.
width > 0 ==>
n < 2 ** width ==>
v2n (fixwidth width (n2v n)) = n
Proof
rpt strip_tac >>
gs[bitstringTheory.fixwidth_def] >>
‘LENGTH (n2v n) <= width’ by gs[n2v_LENGTH] >>
gs[] >>
Cases_on ‘LENGTH (n2v n) = width’ >> (
 gs[]
) >>
‘!w v. v2n (zero_extend w v) = v2n v’ suffices_by (
 gs[]
) >>
Induct >- (
 gs[bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
) >>
gs[bitstringTheory.zero_extend_def] >>
strip_tac >>
Cases_on ‘SUC w > LENGTH v’ >- (
 ‘PAD_LEFT F (SUC w) v = F::(PAD_LEFT F w v)’ suffices_by (
  strip_tac >>
  gs[] >>
  REWRITE_TAC[bitstringTheory.v2n] >>
  gs[]
 ) >>
 gs[bitstringTheory.pad_left_extend, GSYM bitstringTheory.extend_cons] >>
 ‘SUC w − LENGTH v = SUC (w − LENGTH v)’ suffices_by (
  rpt strip_tac >>
  gs[]
 ) >>
 gs[]
) >>
gs[bitstringTheory.zero_extend_def, listTheory.PAD_LEFT, listTheory.GENLIST] >>
‘SUC w − LENGTH v = 0’ by gs[] >>
ASM_REWRITE_TAC[] >>
gs[]
QED

fun brute_subtraction_tac (width:int) =
 let
(*
val width = 2
*)
  val desc = "subtraction"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
  val w2v_tm = fst $ dest_comb $ bitstringSyntax.mk_w2v (wordsSyntax.mk_wordii (0, width))
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   gvs[bitv_binop_inner_def, bitv_sub_def, get_word_binop_def] >>
   gs[bitstringTheory.ops_to_n2w] >>
   simp[wordsTheory.word_2comp_def] >>
   fs[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
   fs[binop_exec_def, bitv_binop_def, get_bitv_binop_def, bitv_sub_def, bitv_add_def, AllCaseEqs()] >>
   gs[prove_binop_add_correct_inner width] >>
   FULL_SIMP_TAC std_ss [bitv_unop_old_def, unop_exec_def, get_word_unop_def, bitv_2comp_def, bitv_1comp_def, bitstringTheory.word_1comp_v2w, bitstringTheory.bnot_def] >>
   rw[bitstringTheory.ops_to_n2w] >>
   Cases_on ‘v2n bl' = 0’ >- (
    fs[] >>
    EVAL_TAC
   ) >>
   FULL_SIMP_TAC std_ss [] >>
   fs[] >>
   assume_tac $ GSYM $ SPEC “((2 ** ^width_tm) − v2n bl')” $ SIMP_RULE (srw_ss()) [] $ INST_TYPE [alpha |-> dim] w2v_n2w >>
   fs[] >>
   assume_tac $ SPEC “^w2v_tm (n2w ((2 ** ^width_tm) − v2n bl'))” bitstringTheory.v2n_lt >>
   gvs[] >>
   fs[bitstringTheory.w2v_v2w] >>
   ‘(v2n (^w2v_tm (n2w ((2 ** ^width_tm) − v2n bl')))) MOD (2 ** ^width_tm) =
        (((2 ** ^width_tm) - 1) * v2n bl') MOD (2 ** ^width_tm)’ suffices_by (
    rpt strip_tac >>
    AP_TERM_TAC >>
    assume_tac (Q.SPECL [‘(2 ** ^width_tm)’, ‘v2n (^w2v_tm (n2w ((2 ** ^width_tm) − v2n bl')))’, ‘((2 ** ^width_tm) - 1) * v2n bl'’, ‘v2n bl’] arithmeticTheory.ADD_MOD) >>
    fs[]
   ) >>
   fs[arithmeticTheory.ADD_MOD] >>
   ‘v2n (^w2v_tm (n2w ((2 ** ^width_tm) − v2n bl'))) = (2 ** ^width_tm) − v2n bl'’ suffices_by (
    rpt strip_tac >>
    fs[] >>
    ‘((2 ** ^width_tm) - 1) * v2n bl' = ((2 ** ^width_tm) - 1) * v2n bl'’ by fs[] >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[arithmeticTheory.RIGHT_SUB_DISTRIB, arithmeticTheory.MULT_LEFT_1] >>
    assume_tac $ Q.SPECL [‘(2 ** ^width_tm)’, ‘v2n bl'’, ‘v2n bl'’] arithmeticTheory.MOD_TIMES_SUB >>
    fs[] >>
    ‘v2n bl' ≤ (2 ** ^width_tm)’ by (
     assume_tac $ Q.SPECL [‘bl'’] bitstringTheory.v2n_lt >>
     rfs[]
    ) >>
    fs[]
   ) >>
   fs[] >>
   qpat_x_assum ‘fixwidth _ _ = _’ (fn thm => REWRITE_TAC[GSYM thm]) >>
   irule sub_lemma >>
   fs[]
  ) >>
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

(* e_sub *)
Theorem binop_sub_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_old binop_sub (bl,n) (bl',n') = SOME (bl'',n'') ==>
binop_exec binop_sub (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def] >>
imp_res_tac bitv_binop_inner >>
brute_arithmetic_tac brute_subtraction_tac 1 128 >>
gs[]
QED

fun brute_saturated_subtraction_tac (width:int) =
 let
(*
val width = 8
*)
  val desc = "saturated subtraction"
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
  val v2w_tm = fst $ dest_comb $ bitstringSyntax.mk_v2w (“a:bool list”, dim)
  val w2n_tm = fst $ dest_comb $ wordsSyntax.mk_w2n (wordsSyntax.mk_wordii (0, width))
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (   
   gvs[bitv_binop_inner_def, wordsTheory.saturate_sub_def, get_word_binop_def] >>
   FULL_SIMP_TAC std_ss [bitstringTheory.ops_to_n2w] >>
   gs[binop_exec_def, bitv_binop_def, get_bitv_binop_def, bitv_saturate_sub_def, AllCaseEqs()] >>
   Cases_on ‘v2n bl' ≤ v2n bl’ >- (
    (* Use wordsTheory.word_sub_w2n, bitstringTheory.w2v_v2w, rest is easy peasy *)
    simp[wordsTheory.n2w_w2n] >>
    assume_tac $ Q.SPECL [‘^v2w_tm bl’, ‘^v2w_tm bl'’] $ INST_TYPE [alpha |-> dim] wordsTheory.word_sub_w2n >>
    fs[wordsTheory.WORD_LS] >>
    ‘^w2n_tm (v2w bl') ≤ ^w2n_tm (v2w bl)’ by (
     simp[GSYM bitstringTheory.n2w_v2n] >>
     ‘v2n bl' MOD (2 ** ^width_tm) = v2n bl' /\ v2n bl MOD (2 ** ^width_tm) = v2n bl’ suffices_by (
      FULL_SIMP_TAC std_ss [] 
     ) >>
     CONJ_TAC >- (
      irule arithmeticTheory.LESS_MOD >>
      assume_tac $ Q.SPECL [‘bl'’] bitstringTheory.v2n_lt >>
      rfs[]
     ) >>
     irule arithmeticTheory.LESS_MOD >>
     assume_tac $ Q.SPECL [‘bl’] bitstringTheory.v2n_lt >>
     rfs[]
    ) >>
    gs[] >>
    qpat_x_assum ‘w2n (v2w bl + -1w * v2w bl') = _’ (fn thm => rewrite_tac[GSYM thm]) >>
    FULL_SIMP_TAC std_ss [] >>
    assume_tac $ GSYM $ INST_TYPE [alpha |-> dim] bitstringTheory.w2v_v2w >>
    FULL_SIMP_TAC std_ss [] >>
    imp_res_tac $ INST_TYPE [alpha |-> dim] wordsTheory.n2w_sub >>
    gs[] >>
    AP_TERM_TAC >>
    assume_tac $ Q.SPECL [‘(2 ** ^width_tm)’] arithmeticTheory.MOD_MOD >>
    EVAL_TAC >>
    AP_TERM_TAC >>
    assume_tac $ Q.SPECL [‘(2 ** ^width_tm)’, ‘(2 ** ^width_tm) − l2n 2 (bitify [] bl') MOD (2 ** ^width_tm)’, ‘((2 ** ^width_tm) - 1) * l2n 2 (bitify [] bl')’, ‘l2n 2 (bitify [] bl)’] arithmeticTheory.ADD_MOD >>
    ‘0 < (2 ** ^width_tm)’ by simp[] >>
    FULL_SIMP_TAC std_ss [] >>
    fs[] >>
    assume_tac $ GSYM $ Q.SPECL [‘(2 ** ^width_tm)’, ‘l2n 2 (bitify [] bl') MOD (2 ** ^width_tm)’, ‘l2n 2 (bitify [] bl') MOD (2 ** ^width_tm)’] arithmeticTheory.MOD_TIMES_SUB >>
    FULL_SIMP_TAC std_ss [] >>
    fs[] >>
    Cases_on ‘l2n 2 (bitify [] bl') MOD (2 ** ^width_tm) = 0’ >- (
     fs[GSYM bitstringTheory.v2n_def] >>
     ‘v2n bl' = 0’ suffices_by simp[] >>
     ‘v2n bl' < (2 ** ^width_tm)’ suffices_by (
      rpt strip_tac >>
      imp_res_tac arithmeticTheory.MOD_EQ_0_IFF >>
      FULL_SIMP_TAC std_ss []
     ) >>
     assume_tac $ Q.SPECL [‘bl'’] bitstringTheory.v2n_lt >>
     REV_FULL_SIMP_TAC std_ss []
    ) >>
    ‘0 < l2n 2 (bitify [] bl') MOD (2 ** ^width_tm) ∧
           l2n 2 (bitify [] bl') MOD (2 ** ^width_tm) ≤ (2 ** ^width_tm)’ suffices_by (
     FULL_SIMP_TAC std_ss [arithmeticTheory.MOD_MOD]
    ) >>
    fs[] >>
    irule arithmeticTheory.LT_IMP_LE >>
    irule arithmeticTheory.MOD_LESS >>
    simp[]
   ) >>
   fs[] >>
   ‘w2n (^v2w_tm bl) − w2n (^v2w_tm bl') = 0’ by (
    simp[GSYM bitstringTheory.n2w_v2n] >>
    ‘v2n bl' MOD (2 ** ^width_tm) = v2n bl' /\ v2n bl MOD (2 ** ^width_tm) = v2n bl’ suffices_by (
     fs[]
    ) >>
    CONJ_TAC >- (
     irule arithmeticTheory.LESS_MOD >>
     assume_tac $ Q.SPECL [‘bl'’] bitstringTheory.v2n_lt >>
     gs[]
    ) >>
    irule arithmeticTheory.LESS_MOD >>
    assume_tac $ Q.SPECL [‘bl’] bitstringTheory.v2n_lt >>
    gs[]
   ) >>
   ASM_REWRITE_TAC[prove(“^(wordsSyntax.mk_wordii (0,width)) = v2w [F]”, blastLib.BBLAST_TAC)] >>
   REWRITE_TAC[bitstringTheory.w2v_v2w] >>
   fs[bitstringTheory.n2v_def, bitstringTheory.boolify_def, bitstringTheory.fixwidth_def]
  ) >>
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’ (fn thm => let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

Theorem binop_sat_sub_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
LENGTH bl' = n ==>
bitv_binop_old binop_sat_sub (bl,n) (bl',n') = SOME (bl'',n'') ==>
binop_exec binop_sat_sub (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def] >>
imp_res_tac bitv_binop_inner >>
(* Takes 1263.138s *)
brute_arithmetic_tac brute_saturated_subtraction_tac 1 2 >>
gs[]
QED

(* e_shl *)
Theorem binop_shl_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
n <= 128 ==>
n > 0 ==>
bitv_bl_binop shiftl (bl,n) ((\(bl, n). (v2n bl, n)) (bl',n')) = (bl'',n'') ==>
binop_exec binop_shl (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_bl_binop_def] >>
gvs[bitv_binop_inner_def, bitv_bl_binop_def, wordsTheory.word_lsl_bv_def] >>
gs[binop_exec_def, bitv_bl_binop_def, AllCaseEqs()]
QED

(* e_shl *)
Theorem binop_shr_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = n ==>
n <= 128 ==>
n > 0 ==>
bitv_bl_binop shiftr (bl,n) ((\(bl, n). (v2n bl, n)) (bl',n')) = (bl'',n'') ==>
binop_exec binop_shr (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_bl_binop_def] >>
gvs[bitv_binop_inner_def, bitv_bl_binop_def, wordsTheory.word_lsr_bv_def] >>
gs[binop_exec_def, bitv_bl_binop_def, AllCaseEqs()] >>
gs[bitstringTheory.shiftr_def] >>
Cases_on ‘v2n bl' ≤ LENGTH bl’ >- (
 gs[]
) >>
‘LENGTH bl − v2n bl' = 0’ by gs[] >>
ASM_REWRITE_TAC[] >>
gs[]
QED

(* TODO: Don't hard-code "n" *)
(* TODO: Merge with arithmetic_tac? *)
fun brute_predicate_tac' desc (width:int) =
 let
(*
val width = 1
val desc = "test"
*)
  val width_num = Arbnum.fromInt width
  val width_tm = numSyntax.term_of_int width
  val width_minus_one_tm = numSyntax.term_of_int (width-1)
  val dim = fcpLib.index_type width_num
 in
  tmCases_on (mk_eq(mk_var("n", numSyntax.num), numSyntax.term_of_int width)) ["eq", "neq"] >- (
   ‘LENGTH bl = ^width_tm’ by gs[] >>
   ‘LENGTH bl' = ^width_tm’ by gs[] >>
   gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
   FULL_SIMP_TAC std_ss [bitstringTheory.ops_to_n2w] >>
   fs[binop_exec_def, bitv_bl_binop_def, bitv_binpred_def, get_bitv_binpred_def, bitv_ls_def, bitv_hs_def, bitv_lo_def, bitv_hi_def, wordsTheory.WORD_LS, wordsTheory.WORD_HS, wordsTheory.WORD_LO, wordsTheory.WORD_HI, AllCaseEqs()] >>
   ‘v2n bl = v2n bl MOD (^(wordsSyntax.mk_dimword dim)) /\
    v2n bl' = v2n bl' MOD (^(wordsSyntax.mk_dimword dim))’ suffices_by (
    fs[]
   ) >>
   FULL_SIMP_TAC std_ss [arithmeticTheory.X_MOD_Y_EQ_X] >>
   assume_tac $ Q.SPEC ‘bl’ bitstringTheory.v2n_lt >>
   assume_tac $ Q.SPEC ‘bl'’ bitstringTheory.v2n_lt >>
   rfs[]
  ) >>
  (* All except last *)
  TRY $ ‘n > ^width_tm’ by gs[] >>
   TRY (
    qpat_assum ‘n > ^width_tm’
     (fn thm =>
      let val _ = print ("Proved correctness of "^desc^" with width "^(Int.toString width)^"...\n") in ALL_TAC end) >>
    TRY $ qpat_x_assum ‘n > ^width_minus_one_tm’ (fn thm => ALL_TAC) >>
    qpat_x_assum ‘n <> ^width_tm’ (fn thm => ALL_TAC)
  )
 end
;

(*
val desc = "test"
val min = 1
val max = 1
*)
fun brute_predicate_tac desc min max =
 let
  val widths = upto min max
  val tacs = map (fn width => brute_predicate_tac' desc width) widths
 in
  foldr (op THEN) ALL_TAC tacs
 end
;


(* e_le *)
Theorem binop_le_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
bitv_binpred_old binop_le (bl,n) (bl',n') = SOME b ==>
binop_exec binop_le (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binpred_old_def] >>
imp_res_tac bitv_binpred_inner >>
brute_predicate_tac "less-or-equal" 1 128 >>
gs[]
QED

(* e_ge *)
Theorem binop_ge_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
bitv_binpred_old binop_ge (bl,n) (bl',n') = SOME b ==>
binop_exec binop_ge (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binpred_old_def] >>
imp_res_tac bitv_binpred_inner >>
brute_predicate_tac "greater-or-equal" 1 128 >>
gs[]
QED

(* e_lt *)
Theorem binop_lt_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
bitv_binpred_old binop_lt (bl,n) (bl',n') = SOME b ==>
binop_exec binop_lt (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binpred_old_def] >>
imp_res_tac bitv_binpred_inner >>
brute_predicate_tac "less-than" 1 128 >>
gs[]
QED

(* e_gt *)
Theorem binop_gt_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
bitv_binpred_old binop_gt (bl,n) (bl',n') = SOME b ==>
binop_exec binop_gt (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binpred_old_def] >>
imp_res_tac bitv_binpred_inner >>
brute_predicate_tac "greater-than" 1 128 >>
gs[]
QED

(* e_neq *)
Theorem binop_neq_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
((bl,n) <> (bl',n')) = b ==>
binop_exec binop_neq (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def] >>
gs[binop_exec_def]
QED

(* e_neq_bool *)
Theorem binop_neq_bool_correct:
!b b' b''.
(b <> b') = b'' ==>
binop_exec binop_neq (v_bool b) (v_bool b') = SOME (v_bool b'')
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def, binop_exec_def]
QED

(* e_eq *)
Theorem binop_eq_correct:
!bl n bl' n' b.
LENGTH bl = n ==>
LENGTH bl' = n' ==>
((bl,n) = (bl',n')) = b ==>
binop_exec binop_eq (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bool b)
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def] >>
gs[binop_exec_def]
QED

(* e_eq_bool *)
Theorem binop_eq_bool_correct:
!b b' b''.
(b = b') = b'' ==>
binop_exec binop_eq (v_bool b) (v_bool b') = SOME (v_bool b'')
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def, binop_exec_def]
QED


(* e_and *)
Theorem binop_and_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = LENGTH bl' ==>
bitv_bl_binop band (bl,n) (bl',n') = (bl'',n'') ==>
binop_exec binop_and (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def] >>
gvs[bitv_binop_inner_def, bitv_bl_binop_def] >>
gs[binop_exec_def, bitv_bl_binop_def, band'_def, bitstringTheory.band_def, bitstringTheory.bitwise_def] >>
‘(λ(x,y). x ∧ y) = (UNCURRY $/\)’ suffices_by (
 gs[]
) >>
gs[boolTheory.AND_DEF]
QED

(* e_xor *)
Theorem binop_xor_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = LENGTH bl' ==>
bitv_bl_binop bxor (bl,n) (bl',n') = (bl'',n'') ==>
binop_exec binop_xor (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def] >>
gvs[bitv_binop_inner_def, bitv_bl_binop_def] >>
gs[binop_exec_def, bitv_bl_binop_def]
QED

(* e_or *)
Theorem binop_or_correct:
!bl n bl' n' bl'' n''.
LENGTH bl = LENGTH bl' ==>
bitv_bl_binop bor (bl,n) (bl',n') = (bl'',n'') ==>
binop_exec binop_or (v_bit (bl,n)) (v_bit (bl',n')) = SOME (v_bit (bl'',n''))
Proof
rpt strip_tac >>
gs[bitv_binop_old_def, bitv_binpred_def] >>
gvs[bitv_binop_inner_def, bitv_bl_binop_def] >>
gs[binop_exec_def, bitv_bl_binop_def, bor'_def, bitstringTheory.bor_def, bitstringTheory.bitwise_def] >>
‘(λ(x:bool,y). x \/ y) = (UNCURRY $\/)’ suffices_by (
 gs[]
) >>
gs[boolTheory.OR_DEF]
QED

(* e_bin_and1 *)
Theorem binop_bin_and1_correct:
!e_ctx g_scope_list scope_list e.
e_exec e_ctx g_scope_list scope_list (e_binop (e_v $ v_bool F) binop_bin_and e) = SOME (e_v (v_bool F), [])
Proof
rpt strip_tac >>
gs[e_exec_def, is_short_circuitable_def, e_exec_short_circuit_def]
QED

(* e_bin_and2 *)
Theorem binop_bin_and2_correct:
!e_ctx g_scope_list scope_list e.
e_exec e_ctx g_scope_list scope_list (e_binop (e_v $ v_bool T) binop_bin_and e) = SOME (e, [])
Proof
rpt strip_tac >>
gs[e_exec_def, is_short_circuitable_def, e_exec_short_circuit_def]
QED

(* e_bin_or1 *)
Theorem binop_bin_or1_correct:
!e_ctx g_scope_list scope_list e.
e_exec e_ctx g_scope_list scope_list (e_binop (e_v $ v_bool T) binop_bin_or e) = SOME (e_v (v_bool T), [])
Proof
rpt strip_tac >>
gs[e_exec_def, is_short_circuitable_def, e_exec_short_circuit_def]
QED

(* e_bin_or2 *)
Theorem binop_bin_or2_correct:
!e_ctx g_scope_list scope_list e.
e_exec e_ctx g_scope_list scope_list (e_binop (e_v $ v_bool F) binop_bin_or e) = SOME (e, [])
Proof
rpt strip_tac >>
gs[e_exec_def, is_short_circuitable_def, e_exec_short_circuit_def]
QED

val _ = export_theory ();
