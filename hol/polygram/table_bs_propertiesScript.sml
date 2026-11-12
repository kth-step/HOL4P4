open HolKernel boolLib simpLib Parse bossLib;
open blastLib bitstringLib;
open wordsLib;

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



(******************************************************************)
(* Width-generic helper lemmas.                                   *)
(* Each fact is proved once for an arbitrary word type 'a and     *)
(* then instantiated at the widths 1..128 used by the bitv_*      *)
(* definitions, so the proofs below never evaluate or bit-blast   *)
(* 128 separate word widths.                                      *)
(******************************************************************)

val w2n_v2w_mod = prove(
  “w2n (v2w v : 'a word) = v2n v MOD 2 ** dimindex(:'a)”,
  simp[w2n_v2w, bitTheory.MOD_2EXP_def]);

val v2n_fixwidth_dimindex = prove(
  “v2n (fixwidth (dimindex(:'a)) v) = v2n v MOD 2 ** dimindex(:'a)”,
  ‘v2n (fixwidth (dimindex(:'a)) v) =
   v2n (fixwidth (dimindex(:'a)) v) MOD 2 ** dimindex(:'a)’
     by (irule (GSYM arithmeticTheory.LESS_MOD) >>
         metis_tac[v2n_lt, length_fixwidth]) >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[GSYM w2n_v2w_mod, v2w_fixwidth]);

val fixwidth_eq_dimindex = prove(
  “fixwidth (dimindex(:'a)) v = fixwidth (dimindex(:'a)) w ⇔
   v2n v MOD 2 ** dimindex(:'a) = v2n w MOD 2 ** dimindex(:'a)”,
  simp[GSYM v2w_11, GSYM w2n_v2w_mod] >> metis_tac[w2n_11]);

val v2n_w2v_w2n = prove(
  “v2n (w2v (w : 'a word)) = w2n w”,
  ‘v2n (w2v w) = v2n (w2v w) MOD 2 ** dimindex(:'a)’
     by (irule (GSYM arithmeticTheory.LESS_MOD) >>
         metis_tac[v2n_lt, length_w2v]) >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[GSYM w2n_v2w_mod, v2w_w2v]);

val w2n_add_mod = prove(
  “w2n (a + b : 'a word) = (w2n a + w2n b) MOD 2 ** dimindex(:'a)”,
  simp[word_add_def, w2n_n2w, dimword_def]);

val w2n_sub_mod = prove(
  “w2n (a - b : 'a word) =
   (w2n a + (2 ** dimindex(:'a) - w2n b)) MOD 2 ** dimindex(:'a)”,
  simp[word_sub_def, word_2comp_def, word_add_def, w2n_n2w, dimword_def] >>
  ‘w2n b < 2 ** dimindex(:'a)’ by metis_tac[w2n_lt, dimword_def] >>
  Cases_on ‘w2n b = 0’ >> gvs[]);


(* instantiate a width-generic theorem at the word width k *)
fun inst_width k th =
  let
    val ty = fcpSyntax.mk_int_numeric_type k
    val dim_thm = if k = 1 then fcpTheory.index_one
                  else fcpLib.INDEX_CONV (fcpSyntax.mk_dimindex ty)
  in
    PURE_REWRITE_RULE [dim_thm] (INST_TYPE [alpha |-> ty] th)
  end;

(* proves  ∀n. n < 129 ⇒ 0 < n ⇒ body  by closing the case of each
   width k (k = 128, ..., 1) with  tac k *)
fun prove_for_widths (body : term) (tac : int -> tactic) =
  let
    val n = mk_var("n", numSyntax.num)
    val goal = mk_forall(n,
                 mk_imp(numSyntax.mk_less(n, numSyntax.term_of_int 129),
                        mk_imp(numSyntax.mk_less(numSyntax.zero_tm, n), body)))
    fun loop 0 = CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >> simp[]
      | loop k = CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
                 conj_tac >- tac k >> loop (k-1)
  in
    prove(goal, loop 128)
  end;

(* the clause for width k of bitv_binpred_inner / bitv_binop_inner *)
fun binpred_clause k = GEN_ALL (el k (CONJUNCTS bitv_binpred_inner_def));
fun binop_clause   k = GEN_ALL (el k (CONJUNCTS bitv_binop_inner_def));

(* bitv_binpred_inner with an unsigned comparison is that comparison
   on the numeric values modulo 2 ** n *)
fun binpred_nat_thm opr rel word_thm =
  prove_for_widths
    “∀v v'. bitv_binpred_inner ^opr v v' n =
            SOME (^rel (v2n v MOD 2 ** n) (v2n v' MOD 2 ** n))”
    (fn k => rewrite_tac[binpred_clause k, get_word_binpred_def, word_thm,
                         inst_width k w2n_v2w_mod] >>
             simp[]);

val binpred_inner_nat = LIST_CONJ [
  binpred_nat_thm “binop_le” “$<= : num -> num -> bool” WORD_LS,
  binpred_nat_thm “binop_ge” “$>= : num -> num -> bool” WORD_HS,
  binpred_nat_thm “binop_lt” “$< : num -> num -> bool”  WORD_LO,
  binpred_nat_thm “binop_gt” “$> : num -> num -> bool”  WORD_HI];

val v2n_fixwidth = prove_for_widths
  “∀v. v2n (fixwidth n v) = v2n v MOD 2 ** n”
  (fn k => simp[inst_width k v2n_fixwidth_dimindex]);

val fixwidth_eq_v2n = prove_for_widths
  “∀v w. fixwidth n v = fixwidth n w ⇔ v2n v MOD 2 ** n = v2n w MOD 2 ** n”
  (fn k => simp[inst_width k fixwidth_eq_dimindex]);

val binpred_inner_some = prove_for_widths
  “∀b v v'. bitv_binpred_inner b v v' n ≠ NONE”
  (fn k => simp[binpred_clause k]);

val binop_inner_some = prove_for_widths
  “∀b v v'. ∃r. bitv_binop_inner b v v' n = SOME (r, n)”
  (fn k => simp[binop_clause k]);

val binop_inner_add = prove_for_widths
  “∀v v'. ∃r. bitv_binop_inner binop_add v v' n = SOME (r, n) ∧
              v2n r = (v2n v MOD 2 ** n + v2n v' MOD 2 ** n) MOD 2 ** n”
  (fn k => simp[binop_clause k, get_word_binop_def, inst_width k v2n_w2v_w2n,
                inst_width k w2n_add_mod, inst_width k w2n_v2w_mod]);

val binop_inner_sub = prove_for_widths
  “∀v v'. ∃r. bitv_binop_inner binop_sub v v' n = SOME (r, n) ∧
              v2n r = (v2n v MOD 2 ** n + (2 ** n - v2n v' MOD 2 ** n)) MOD 2 ** n”
  (fn k => simp_tac std_ss [binop_clause k] >>
           rewrite_tac[get_word_binop_def, inst_width k v2n_w2v_w2n,
                       inst_width k w2n_sub_mod, inst_width k w2n_v2w_mod] >>
           simp[]);

(* outside the widths 1..128 both inner functions are NONE *)
val binpred_inner_none = prove(
  “∀b v v' n. bitv_binpred_inner b v v' n = NONE ⇔ n = 0 ∨ 128 < n”,
  rpt gen_tac >> eq_tac
  >- (CCONTR_TAC >> gvs[] >>
      ‘n < 129 ∧ 0 < n’ by decide_tac >> metis_tac[binpred_inner_some])
  >> strip_tac >> ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt (IF_CASES_TAC >- fs[]) >> rewrite_tac[]);

val binop_inner_none = prove(
  “∀b v v' n. bitv_binop_inner b v v' n = NONE ⇔ n = 0 ∨ 128 < n”,
  rpt gen_tac >> eq_tac
  >- (CCONTR_TAC >> gvs[] >>
      ‘n < 129 ∧ 0 < n’ by decide_tac >>
      metis_tac[binop_inner_some, NOT_NONE_SOME])
  >> strip_tac >> ONCE_REWRITE_TAC [bitv_binop_inner_def] >>
  rpt (IF_CASES_TAC >- fs[]) >> rewrite_tac[]);


(* arithmetic on values modulo 2 ** n *)
val mod_exp_facts = prove(
  “(∀x n. x MOD 2 ** n < 2 ** n) ∧
   (∀x n. x MOD 2 ** n ≤ 2 ** n - 1) ∧
   (∀x n. ¬(2 ** n - 1 < x MOD 2 ** n)) ∧
   (∀x n. ¬(x MOD 2 ** n > 2 ** n - 1)) ∧
   (∀x n. (x MOD 2 ** n) MOD 2 ** n = x MOD 2 ** n) ∧
   (∀n. (2 ** n - 1) MOD 2 ** n = 2 ** n - 1) ∧
   (∀n. 0 MOD 2 ** n = 0) ∧
   (∀n. 0 < n ⇒ 1 MOD 2 ** n = 1)”,
  ‘∀x n. x MOD 2 ** n < 2 ** n’
    by simp[arithmeticTheory.MOD_LESS, bitTheory.ZERO_LT_TWOEXP] >>
  rpt conj_tac >> rpt gen_tac
  >- simp[]
  >- (first_x_assum (qspecl_then [‘x’, ‘n’] mp_tac) >> decide_tac)
  >- (first_x_assum (qspecl_then [‘x’, ‘n’] mp_tac) >> decide_tac)
  >- (first_x_assum (qspecl_then [‘x’, ‘n’] mp_tac) >> decide_tac)
  >- simp[arithmeticTheory.MOD_MOD, bitTheory.ZERO_LT_TWOEXP]
  >- (irule arithmeticTheory.LESS_MOD >> simp[bitTheory.ZERO_LT_TWOEXP])
  >- simp[arithmeticTheory.ZERO_MOD, bitTheory.ZERO_LT_TWOEXP]
  >> strip_tac >> irule arithmeticTheory.LESS_MOD >>
  simp[arithmeticTheory.ONE_LT_EXP]);

val mod_pred = prove(
  “∀x M. 0 < M ∧ x MOD M ≠ 0 ⇒ (x + (M - 1)) MOD M = x MOD M - 1”,
  rpt strip_tac >>
  ‘x MOD M < M’ by simp[arithmeticTheory.MOD_LESS] >>
  ‘x = x DIV M * M + x MOD M’ by metis_tac[arithmeticTheory.DIVISION] >>
  ‘x + (M - 1) = (x DIV M + 1) * M + (x MOD M - 1)’
    by (rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  irule arithmeticTheory.MOD_MULT >> decide_tac);

val mod_succ = prove(
  “∀x M. x MOD M + 1 < M ⇒ (x + 1) MOD M = x MOD M + 1”,
  rpt strip_tac >>
  ‘0 < M’ by decide_tac >>
  ‘x = x DIV M * M + x MOD M’ by metis_tac[arithmeticTheory.DIVISION] >>
  ‘x + 1 = x DIV M * M + (x MOD M + 1)’ by decide_tac >>
  pop_assum SUBST1_TAC >>
  irule arithmeticTheory.MOD_MULT >> decide_tac);

(* exported so that dependent theories can reason about bit vectors
   through their numeric values instead of splitting on 128 widths *)
Theorem bitv_binpred_inner_nat = binpred_inner_nat
Theorem bitv_v2n_fixwidth = v2n_fixwidth
Theorem bitv_fixwidth_eq_v2n = fixwidth_eq_v2n
Theorem bitv_binpred_inner_some = binpred_inner_some
Theorem bitv_binop_inner_some = binop_inner_some
Theorem bitv_binop_inner_add = binop_inner_add
Theorem bitv_binop_inner_sub = binop_inner_sub
Theorem bitv_binpred_inner_none = binpred_inner_none
Theorem bitv_binop_inner_none = binop_inner_none
Theorem bitv_mod_exp_facts = mod_exp_facts
Theorem bitv_mod_pred = mod_pred
Theorem bitv_mod_succ = mod_succ

val nat_ss = [binpred_inner_nat, v2n_fixwidth, v2n_n2v, max_from_type_def,
              mod_exp_facts];



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
  rw[bitv_binpred_def] >>
  ‘bitv_binpred_inner binop_any bv10 bv20 bv11 ≠ NONE’ by simp[] >>
  gvs[binpred_inner_none]
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
  rw[bitv_binop_def] >>
  ‘bv11 < 129 ∧ 0 < bv11’ by decide_tac >>
  qspecl_then [‘bv11’] mp_tac binop_inner_some >>
  simp[] >>
  disch_then (qspecl_then [‘binop_any’, ‘bv10’, ‘bv20’] strip_assume_tac) >>
  gvs[]
QED


Theorem all_bs_larger_than_zero:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_ge (bl,len) (fixwidth len (n2v 0),len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  simp nat_ss
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



Theorem all_bs_larger_than_zero2:
  ∀ len bl bl'.
    len > 0 ∧ len < 129 ∧
    fixwidth len bl' = fixwidth len (n2v 0) ⇒
    bitv_binpred binop_ge (bl,len) (bl',len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  ‘v2n bl' MOD 2 ** len = 0’ by gvs (fixwidth_eq_v2n :: nat_ss) >>
  simp nat_ss
QED




(* theorem of
   (∀a b. a ≠ 0w ⇒ (b ≤₊ a − 1w ⇔ ¬(b ≥₊ a)))
*)

val word_ineq_generic = prove(
  “∀(a : 'a word) b. a ≠ 0w ⇒ (b ≤₊ a − 1w ⇔ ¬(b ≥₊ a))”,
  rpt strip_tac >>
  imp_res_tac SUC_WORD_PRED >>
  rewrite_tac[WORD_LS, WORD_HS] >>
  decide_tac);

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
    prove(goal, MATCH_ACCEPT_TAC (inst_width len word_ineq_generic))
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
  ‘len < 129 ∧ 0 < len’ by decide_tac >>
  ‘v2n n MOD 2 ** len ≠ 0’ by gvs (fixwidth_eq_v2n :: nat_ss) >>
  qspecl_then [‘len’] mp_tac binop_inner_sub >>
  simp[] >>
  disch_then (qspecl_then [‘n’, ‘n2v 1’] strip_assume_tac) >>
  gvs[bitv_binop_def, bitv_binpred_def] >>
  gvs nat_ss >>
  ‘(v2n n + (2 ** len − 1)) MOD 2 ** len = v2n n MOD 2 ** len − 1’
    by simp[mod_pred, bitTheory.ZERO_LT_TWOEXP] >>
  simp[]
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
  rpt strip_tac >>
  gvs[binpred_inner_none]
QED




Theorem last_edge_of_binop_bs:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binop_inner binpred v v' n = NONE ⇒
    n > 128
Proof
  rpt strip_tac >>
  gvs[binop_inner_none]
QED




Theorem no_bs_is_larger_than_the_largest:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_gt n (n2v (max_from_type n')) (n':num) = SOME F
Proof
  rpt strip_tac >>
  ‘n' < 129 ∧ 0 < n'’ by decide_tac >>
  simp nat_ss
QED



Theorem no_bs_is_less_that_the_least:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_lt n (n2v 0) n' = SOME F
Proof
  rpt strip_tac >>
  ‘n' < 129 ∧ 0 < n'’ by decide_tac >>
  simp nat_ss
QED



Theorem max_ge_max_thm:
  ∀ len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_ge (n2v (max_from_type len),len) (n2v (max_from_type len),len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  simp nat_ss
QED







Theorem every_bs_is_less_than_max:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_le (bl,len) (n2v (max_from_type len),len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  simp nat_ss
QED



(*
(∀a b. a <₊ n2w (max_from_type n) ⇒ (a + 1w ≤₊ b ⇔ a <₊ b))
*)

val gen_max_bound_generic = prove(
  “∀(a : 'a word) b.
     a <₊ n2w (2 ** dimindex(:'a) - 1) ⇒ (a + 1w ≤₊ b ⇔ a <₊ b)”,
  rpt strip_tac >>
  ‘w2n (n2w (2 ** dimindex(:'a) - 1) : 'a word) = 2 ** dimindex(:'a) - 1’
    by simp[w2n_n2w, dimword_def, mod_exp_facts] >>
  ‘w2n (1w : 'a word) = 1’ by simp[w2n_n2w, ONE_LT_dimword] >>
  gvs[WORD_LO, WORD_LS] >>
  ‘w2n (a + 1w) = w2n a + 1’
    by (simp[w2n_add_mod] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  simp[]);

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
                 rewrite_tac[max_from_type_def] >>
                 MATCH_ACCEPT_TAC (inst_width len gen_max_bound_generic))
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
  ‘len < 129 ∧ 0 < len’ by decide_tac >>
  qspecl_then [‘len’] mp_tac binop_inner_add >>
  simp[] >>
  disch_then (qspecl_then [‘n’, ‘n2v 1’] strip_assume_tac) >>
  gvs[bitv_binop_def, bitv_binpred_def] >>
  gvs nat_ss >>
  ‘v2n n MOD 2 ** len + 1 < 2 ** len’ by decide_tac >>
  ‘(v2n n + 1) MOD 2 ** len = v2n n MOD 2 ** len + 1’ by simp[mod_succ] >>
  ‘(v2n n MOD 2 ** len + 1) MOD 2 ** len = v2n n MOD 2 ** len + 1’
    by (irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  simp[]
QED





val w_is_less_than_max_fixwidth_generic = prove(
  “∀(a : 'a word).
     a ≤₊ v2w (fixwidth (dimindex(:'a)) (n2v (2 ** dimindex(:'a) - 1)))”,
  rpt strip_tac >>
  ‘w2n a < 2 ** dimindex(:'a)’ by metis_tac[w2n_lt, dimword_def] >>
  simp[v2w_fixwidth, v2w_n2v, WORD_LS, w2n_n2w, dimword_def, mod_exp_facts]);

fun w_is_less_than_max_fixwidth_thm len =
let
  val size_term = numSyntax.term_of_int len
  val word_ty = wordsSyntax.mk_int_word_type len

    val a = mk_var("a", word_ty)

  val goal =
    “∀ a . ^a ≤₊ v2w (fixwidth ^size_term (n2v (max_from_type ^size_term ))) ”;

  val thm = prove(goal,
                 rewrite_tac[max_from_type_def] >>
                 MATCH_ACCEPT_TAC (inst_width len w_is_less_than_max_fixwidth_generic))
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
  rw[bitv_binpred_def] >>
  simp nat_ss
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
  rw[bitv_binpred_def] >>
  simp nat_ss
QED



Theorem transitive_binpred1:
  ∀ len a b c.
    len < 129 ∧  len > 0 ∧
    bitv_binpred binop_le (a,len) (b,len) = SOME T ∧
    bitv_binpred binop_ge (a,len) (c,len) = SOME T ⇒
    bitv_binpred binop_gt (c,len) (b,len) = SOME F
Proof
  rw[bitv_binpred_def] >>
  gvs nat_ss
QED





val _ = export_theory ();



