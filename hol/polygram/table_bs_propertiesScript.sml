open HolKernel boolLib simpLib Parse bossLib;
open blastLib bitstringLib;

open p4Theory;
open p4_auxTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;



val _ = new_theory "table_bs_properties";



Definition max_from_type_def:
  max_from_type type =
  (2:num) ** type - (1:num)
End


Theorem bitv_binpred_same_length:
  ∀ binop_any bv1 bv2 x.
    bitv_binpred binop_any bv1 bv2 = SOME x ⇒
    (SND bv1 = SND bv2)
Proof
  rpt gen_tac >>
  PairCases_on ‘bv1’ >>
  PairCases_on ‘bv2’ >>
  
  gvs[bitv_binpred_def]
QED


Theorem bitv_binpred_range_length:
  ∀ binop_any bv1 bv2 x.
    bitv_binpred binop_any bv1 bv2 = SOME x ⇒
    (SND bv1 > 0 ∧ SND bv1 < 129)
Proof
  rpt gen_tac >>
  PairCases_on ‘bv1’ >>
  PairCases_on ‘bv2’ >>
  
  gvs[bitv_binpred_def] >>

  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
      
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[] >>
      intLib.COOPER_TAC
     )) >>
  intLib.COOPER_TAC 
QED


Theorem bitv_binop_range_length:
  ∀ binop_any bv1 bv2 bv3.
    (SND bv2 > 0 ∧ SND bv2 < 129) ∧
    bitv_binop binop_any bv1 bv2 = SOME bv3 ⇒
    (SND bv3 = SND bv2)
Proof
  rpt gen_tac >>
  PairCases_on ‘bv1’ >>
  PairCases_on ‘bv2’ >>
  PairCases_on ‘bv3’ >>
  
  Rewrite.ONCE_REWRITE_TAC [bitv_binop_def] >>
  gvs[] >>

  Rewrite.ONCE_REWRITE_TAC [bitv_binop_inner_def] >>
  rpt strip_tac >>
      
  rpt (
    BasicProvers.FULL_CASE_TAC >-
     fs[]
    ) >>
  intLib.COOPER_TAC 
QED


Theorem all_bs_larger_than_zero:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_ge (bl,len) (fixwidth len (n2v 0),len) = SOME T
Proof                                   
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  rpt strip_tac >>
  gvs[] >>
  
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>

  rpt (
    BasicProvers.FULL_CASE_TAC >-                         
     (gvs[] >>
      gvs[get_word_binpred_def] >>
      EVAL_TAC
     )
    ) >> intLib.COOPER_TAC
QED



Triviality v2w_zero_eq1:
  v2w (fixwidth 128 (n2v 0)) = (0w : word128)
Proof
  EVAL_TAC
QED


Theorem fixed_width_imp_v_words_zero:
  ∀ n.
    n = fixwidth 128 (n2v 0) ⇒ v2w n = (0w : word128)
Proof
  blastLib.FULL_BBLAST_TAC >>
  EVAL_TAC >>
  gvs[]
QED




(* theorem of
   fixwidth 128 bl = fixwidth 128 (n2v 0) ⇒ (v2w bl: word128 word) = v2w (n2v 0)
   ...
   fixwidth 1 bl   = fixwidth 1   (n2v 0) ⇒ (v2w bl: word1 word) = v2w (n2v 0)
*)

fun gen_fixwidth_thm len = let
  val len_term = numSyntax.term_of_int len
  val word_ty = wordsSyntax.mk_int_word_type len
  val bl_var = mk_var("bl", Type‘:bitstring’)

  val lhs = bitstringSyntax.mk_v2w(bl_var, fcpSyntax.mk_int_numeric_type len)
  val rhs = bitstringSyntax.mk_v2w(“n2v 0”, fcpSyntax.mk_int_numeric_type len)

  val premise1 = bitstringSyntax.mk_fixwidth(len_term, bl_var)
  val premise2 = bitstringSyntax.mk_fixwidth(len_term, “n2v 0”)

  val eq = mk_eq(lhs, rhs)
  val premise = mk_eq(premise1,premise2)
  val imp = mk_imp(premise, eq)
  val goal = list_mk_forall([bl_var], imp)

  val thm = prove(goal,gvs[v2w_11] )

in
    thm
end;


val all_fixwidth_thms = List.tabulate(128, fn i => gen_fixwidth_thm (i+1));
val big_thm = LIST_CONJ all_fixwidth_thms;
Theorem fixwidth_zero_all = big_thm





(* takes forever *)
Theorem all_bs_larger_than_zero2:
  ∀ len bl bl'.
    len > 0 ∧ len < 129 ∧
    fixwidth len bl' = fixwidth len (n2v 0) ⇒
    bitv_binpred binop_ge (bl,len) (bl',len) = SOME T
Proof                                           
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  rpt strip_tac >>
  gvs[] >>
  
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  
  rpt
  (
  BasicProvers.FULL_CASE_TAC >-
   (                           
   gvs[] >>
   gvs[get_word_binpred_def] >>
   
   imp_res_tac fixwidth_zero_all >>
   gvs[] >>
   blastLib.FULL_BBLAST_TAC        
   ) 
  ) >>
  intLib.COOPER_TAC
QED




(* theorem of
   (∀a b. a ≠ 0w ⇒ (b ≤₊ a − 1w ⇔ ¬(b ≥₊ a)))
*)


fun gen_word_ineq_thm len = let
    val word_ty = wordsSyntax.mk_int_word_type len
    val a = mk_var("a", word_ty)
    val b = mk_var("b", word_ty)
    val zero = wordsSyntax.mk_wordii (0, len)

    val premise = mk_neg(mk_eq(a, zero))
    val le_expr = wordsSyntax.mk_word_ls(b,
                       wordsSyntax.mk_word_sub(a, wordsSyntax.mk_wordii (1, len)))
    val ge_expr = wordsSyntax.mk_word_hs(b, a)
    val conclusion = mk_eq(le_expr, mk_neg ge_expr)
    val goal = list_mk_forall([a, b], mk_imp(premise, conclusion))
in
    prove(goal, rpt strip_tac >> blastLib.FULL_BBLAST_TAC )
end;

val word_ineq_thms = List.tabulate(128, fn i => gen_word_ineq_thm (i+1));
val word_ineq_all1 = LIST_CONJ word_ineq_thms;
Theorem word_ineq_all_sizes = word_ineq_all1






(*

fixwidth 128 n ≠ fixwidth 128 (n2v 0) ⇒
       (v2w lval_bl ≤₊ v2w n − 1w ⇔ ¬(v2w lval_bl ≥₊ v2w n)
*)

fun prove_ineq2_thm len = let

  val word_ty = wordsSyntax.mk_int_word_type len
  val size_term = numSyntax.term_of_int len
  val n_var = mk_var("n", “:bitstring”)
  val lval_var = mk_var("lval_bl", “:bitstring”)

  val fixwidth_n = bitstringSyntax.mk_fixwidth(size_term, n_var)
  val fixwidth_0 = bitstringSyntax.mk_fixwidth(size_term, “n2v 0”)

  val v2w_n = bitstringSyntax.mk_v2w(n_var, fcpSyntax.mk_int_numeric_type len)
  val v2w_l = bitstringSyntax.mk_v2w(lval_var, fcpSyntax.mk_int_numeric_type len)
  val one = wordsSyntax.mk_wordii(1, len)

  val premise = mk_neg(mk_eq(fixwidth_n, fixwidth_0))
  val sub1 = wordsSyntax.mk_word_sub(v2w_n, one)
  val lhs = wordsSyntax.mk_word_ls(v2w_l, sub1)
  val rhs = mk_neg(wordsSyntax.mk_word_hs(v2w_l, v2w_n))
  val conclusion = mk_eq(lhs, rhs)
  val goal = list_mk_forall([n_var, lval_var], mk_imp(premise, conclusion))

  val thm = prove(goal,
                  rpt strip_tac >>
                  Cases_on ‘^v2w_n = v2w (n2v 0)’ >-
                   gvs[v2w_11] >> gvs[] >>
                  imp_res_tac word_ineq_all1 >>
                  gvs[]
                 )
in
  thm
end;


val word_ineq2_thms = List.tabulate(128, fn i => prove_ineq2_thm (i+1));
val word_ineq_all2 = LIST_CONJ word_ineq2_thms;
Theorem word_ineq_all_sizes2 = word_ineq_all2





Theorem bitv_binpred_ge_bool_conv1:
  ∀ lval_bl n n' len bool.
    fixwidth len n ≠ fixwidth len (n2v 0) ∧
    len > 0 ∧ len < 129 ∧
    bitv_binop binop_sub (n,len) (n2v 1,len) = SOME n' ∧
    bitv_binpred binop_ge (lval_bl,len) (n,len) = SOME bool ⇒
    bitv_binpred binop_le (lval_bl,len) n' = SOME (¬bool)
Proof             
                                                
  rpt strip_tac >>
  PairCases_on ‘n'’ >>
  imp_res_tac bitv_binop_range_length >>
  gvs[] >>
  
  gvs[bitv_binpred_def, bitv_binop_def] >>                                                      
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, bitv_binop_inner_def] >>
  rpt strip_tac >>
  
rpt (    
  BasicProvers.FULL_CASE_TAC >-
   (
   fs[] >>
   gvs[bitv_binop_inner_def, bitv_binpred_inner_def] >>
   gvs[get_word_binpred_def, get_word_binop_def] >>
   fs[] >>
   
   rewrite_tac [Once $ GSYM word_sub_def] >>
   
   imp_res_tac word_ineq_all2 >>
   gvs[]
   )
  ) >>
  intLib.COOPER_TAC
QED






Theorem bs_op_means_same_length:
  ∀ op lval_bs v_bs x.
    SOME x = bitv_binpred op lval_bs v_bs ⇒
    (SND lval_bs = SND v_bs)
Proof
  rpt strip_tac >>
  PairCases_on ‘lval_bs’ >>
  PairCases_on ‘v_bs’ >>
  gvs[bitv_binpred_def]
QED



Theorem last_edge_of_binpred_bs:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binpred_inner binpred v v' n = NONE ⇒
    n > 128
Proof

  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  ntac 128 (BasicProvers.FULL_CASE_TAC >-
             fs[]) >>
  intLib.COOPER_TAC
QED




Theorem last_edge_of_binop_bs:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binop_inner binpred v v' n = NONE ⇒
    n > 128
Proof

  Rewrite.ONCE_REWRITE_TAC [bitv_binop_inner_def] >>
  rpt strip_tac >>
  ntac 128 (BasicProvers.FULL_CASE_TAC >-
             fs[]) >>
  intLib.COOPER_TAC
QED




Theorem no_bs_is_larger_than_the_largest:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_gt n (n2v (max_from_type n')) (n':num) = SOME F
Proof
  rw[max_from_type_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (EVAL_TAC >>
      intLib.COOPER_TAC)) >>
  intLib.COOPER_TAC
QED



Theorem no_bs_is_less_that_the_least:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_lt n (n2v 0) n' = SOME F
Proof
  
  rw[max_from_type_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >- 
     (EVAL_TAC >>
      intLib.COOPER_TAC)) >>
  intLib.COOPER_TAC
QED



Theorem max_ge_max_thm:
  ∀ len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_ge (n2v (max_from_type len),len) (n2v (max_from_type len),len) = SOME T
Proof

  rw[max_from_type_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  gvs[] >>
  rpt strip_tac >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  
  rewrite_tac[get_word_binpred_def] >>
  
                 
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     fs[] 
    ) >>
  intLib.ARITH_TAC
QED







Theorem every_bs_is_less_than_max:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_le (bl,len) (n2v (max_from_type len),len) = SOME T
Proof
  rw[max_from_type_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  gvs[] >>
  rpt strip_tac >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  
  rewrite_tac[get_word_binpred_def] >>
  
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[] >>
      blastLib.FULL_BBLAST_TAC) 
    ) >>
  
  intLib.ARITH_TAC
QED                



(*
(∀a b. a <₊ n2w (max_from_type n) ⇒ (a + 1w ≤₊ b ⇔ a <₊ b))
*)


fun gen_max_bound_thm len =
let
  val size_term = numSyntax.term_of_int len
  val word_ty = wordsSyntax.mk_int_word_type len

    val a = mk_var("a", word_ty)
    val b = mk_var("b", word_ty)

  val goal =
    “∀ a b. ^a <₊ n2w (max_from_type ^size_term) ⇒
      (^a + 1w ≤₊ ^b ⇔ ^a <₊ ^b)”;

  val thm = prove(goal,
                 gvs[max_from_type_def] >>
                 rpt strip_tac >>
                 blastLib.FULL_BBLAST_TAC )
in
  thm
end;

val gen_max_bound_thms = List.tabulate(128, fn i => gen_max_bound_thm (i+1));
val gen_max_bound_all1 = LIST_CONJ gen_max_bound_thms;
Theorem gen_max_bound_all1_sizes = gen_max_bound_all1



Theorem bitv_binpred_le_bool_conv1:
  ∀ len lval_bs n n' bool.
    len > 0 ∧ len < 129 ∧
    bitv_binpred binop_le (lval_bs,len) (n,len) = SOME bool ∧
    bitv_binpred binop_ge (n,len) (n2v (max_from_type len),len) = SOME F ∧
    bitv_binop binop_add (n,len) (n2v 1,len) = SOME n' ⇒
    bitv_binpred binop_ge (lval_bs,len) n' = SOME (¬bool)
Proof
  rpt strip_tac >>
  PairCases_on ‘n'’ >>
  imp_res_tac bitv_binop_range_length >>
  gvs[] >>
  
  gvs[bitv_binpred_def, bitv_binop_def] >>                                                      
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, bitv_binop_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (
     fs[] >>
     gvs[bitv_binop_inner_def, bitv_binpred_inner_def] >>
     gvs[get_word_binpred_def, get_word_binop_def] >>
     fs[] >>
     
     
     
     rpt strip_tac >>
     gvs[WORD_HIGHER_EQ] >>
     gvs[WORD_NOT_LOWER_EQUAL] >>
     gvs[gen_max_bound_all1]
     )
    ) >> intLib.ARITH_TAC
QED 
    




fun w_is_less_than_max_fixwidth_thm len =
let
  val size_term = numSyntax.term_of_int len
  val word_ty = wordsSyntax.mk_int_word_type len

    val a = mk_var("a", word_ty)

  val goal =
    “∀ a . ^a ≤₊ v2w (fixwidth ^size_term (n2v (max_from_type ^size_term ))) ”;

  val thm = prove(goal,
                 gvs[max_from_type_def] >>
                 EVAL_TAC >>
                 blastLib.FULL_BBLAST_TAC )
in
  thm
end;

val w_is_less_than_max_fixwidth_thms = List.tabulate(128, fn i => w_is_less_than_max_fixwidth_thm (i+1));
val w_is_less_than_max_fixwidth_all1 = LIST_CONJ w_is_less_than_max_fixwidth_thms;
Theorem w_is_less_than_max_fixwidth_all1_sizes = w_is_less_than_max_fixwidth_all1







Theorem every_bs_is_less_than_max_fixwidth:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_le (bl,len) (fixwidth len (n2v (max_from_type len)),len) = SOME T
Proof
  rw[] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  gvs[] >>
  rpt strip_tac >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  
  rewrite_tac[get_word_binpred_def] >>
                                    
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (
     fs[] >>
     gvs[w_is_less_than_max_fixwidth_all1]
     ) 
    ) >>
  
  intLib.COOPER_TAC
QED









fun gen_fixwidth_max_thm len = let
  val len_term = numSyntax.term_of_int len
  val goal = “fixwidth ^len_term (n2v (max_from_type ^len_term)) = n2v (max_from_type ^len_term)”;
  val thm = prove(goal, EVAL_TAC)

in
    thm
end;

val all_fixwidth_max_thms = List.tabulate(128, fn i => gen_fixwidth_max_thm (i+1));
val big_thm_max = LIST_CONJ all_fixwidth_max_thms;
Theorem fixwidth_max_all = big_thm_max







Theorem last_edge_of_binpred_neg:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binpred binpred (v,n) (v',n) = NONE ⇒
    n > 128
Proof
  metis_tac[bitv_binpred_def, last_edge_of_binpred_bs]
QED




Theorem last_edge_of_binop_neg:
  ∀ binop v v' n.
    n ≠ 0 ∧
    bitv_binop binop (v,n) (v',n) = NONE ⇒
    n > 128
Proof
  metis_tac[bitv_binop_def, last_edge_of_binop_bs]
QED




Theorem every_bs_is_not_larger_than_max_fixwidth:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_gt (bl,len) (fixwidth len (n2v (max_from_type len)),len) = SOME F
Proof
  rw[max_from_type_def, bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>

  rpt 
  ( BasicProvers.FULL_CASE_TAC >-
     (fs[get_word_binpred_def] >>
     EVAL_TAC >>
      intLib.COOPER_TAC
     )
  ) >> intLib.COOPER_TAC 
QED



Theorem transitive_binpred1:
  ∀ len a b c.
    len < 129 ∧  len > 0 ∧
    bitv_binpred binop_le (a,len) (b,len) = SOME T ∧
    bitv_binpred binop_ge (a,len) (c,len) = SOME T ⇒
    bitv_binpred binop_gt (c,len) (b,len) = SOME F
Proof

  rw[bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>

rpt(
  BasicProvers.FULL_CASE_TAC >-
   (fs[get_word_binpred_def] >>
    gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
    blastLib.FULL_BBLAST_TAC 
   )
  ) >> intLib.COOPER_TAC   
QED    





val _ = export_theory ();



