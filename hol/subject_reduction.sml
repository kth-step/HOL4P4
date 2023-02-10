open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
(*open deterTheory;*)
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open arithmeticTheory;
open alistTheory;
open numeralTheory;



(*tactics*)


fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))

fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))

fun OPEN_STMT_TYP_TAC stmt_term =
(Q.PAT_X_ASSUM ` stmt_typ (t1,t2) t f stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_typ_cases] thm)))

fun INST_FST trm_list = (FIRST_X_ASSUM ((qspecl_then trm_list assume_tac))) >> fs[] ;
fun INST_LAST trm_list = (LAST_X_ASSUM ((qspecl_then trm_list assume_tac))) >> fs[] ;

val EXP_GOAL_TYP_IH_TAC = SIMP_TAC (srw_ss()) [Once e_typ_cases] >> 
                          fs[] >>
                          METIS_TAC [] >>
                          fs[];


(******   Subject Reduction for expression    ******)
val sr_exp_def = Define `
 sr_exp (e) (ty:'a itself) =
 ! e' gscope (scopest:scope list) framel t_scope_list t_scope_list_g T_e tau b
   (c:'a ctx) order delta_g delta_b delta_t delta_x f f_called stmt_called copied_in_scope Prs_n.
       (type_scopes_list  (gscope)  (t_scope_list_g) ) /\
       (type_scopes_list  (scopest) (t_scope_list)) /\
       (star_not_in_sl (scopest)  ) /\
       (WT_c c order t_scope_list_g delta_g delta_b delta_x) /\
       (e_red c gscope scopest e e' framel ) /\
       (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e) tau  b) /\
       (T_e = (order,  f, (delta_g, delta_b, delta_x, delta_t))) ==>
       ((?b'. (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e') tau  b')) /\
       (  (framel = [f_called, [stmt_called] , copied_in_scope] ) ==>
       ? t_scope_list_fr . 
	  frame_typ (t_scope_list_g,t_scope_list_fr)  (order,  f_called , (delta_g, delta_b, delta_x, delta_t))  Prs_n gscope copied_in_scope [stmt_called] ))
`;


(****** Subject reduction for expression list ******)
val sr_exp_list_def = Define `
 sr_exp_list (l : e list) (ty:'a itself) = 
       !(e : e). MEM e l ==> sr_exp (e) (ty:'a itself)
`;


(****** Subject reduction for strexp list ******)
val sr_strexp_list_def = Define `
   sr_strexp_list (l : (string#e) list) (ty:'a itself)
      = !  (e:e) . MEM e (SND (UNZIP l)) ==> sr_exp(e) (ty:'a itself)
`;


(****** Subject reduction for str e tup list ******)
val sr_strexp_tup_def = Define ` 
   sr_strexp_tup (tup : (string#e)) (ty:'a itself)
      =  sr_exp ((SND tup)) (ty:'a itself)
`;





(****** List manipluation theories and lemmas  ******)


(** bitv theories section **)

(*
The bitv_binop_innershould return the same width as the input bitstrings
*)

val bitv_binop_inner_lemma =
prove(``
! q q' q'' r r' binop . bitv_binop_inner binop q q' r = SOME (q'',r') ==>
(r = r') ``,
REPEAT GEN_TAC >>
SIMP_TAC (srw_ss()) [Once bitv_binop_inner_def] >>
NTAC 64 (IF_CASES_TAC >>
FULL_SIMP_TAC std_ss [])
);

val bitv_binop_width_lemma =
prove(``
! bitv bitv' bitv'' binop . bitv_binop binop bitv bitv' = SOME bitv'' ==>
(SND bitv = SND bitv') /\ (SND bitv' = SND bitv'') 
``,
REPEAT STRIP_TAC >>
Cases_on `bitv` >>
Cases_on `bitv'` >>
Cases_on `bitv''` >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
);




val binop_bs_width = prove ( ``
! bitv bitv' bitv'' op . 
bs_width bitv' = bs_width bitv /\
bitv_binop op bitv bitv' = SOME bitv'' ==>
bs_width bitv = bs_width bitv'' ``,
Cases_on `op` >>
REPEAT STRIP_TAC >>
PairCases_on `bitv` >>
PairCases_on `bitv'` >>
PairCases_on `bitv''` >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
);


val bitv_bl_binop_width = prove ( ``
! bitv bitv' op . 
bs_width bitv' = bs_width bitv /\
 (op = shiftl \/ op = shiftr)==>
bs_width bitv =
        bs_width (bitv_bl_binop op bitv ((λ(bl,n). (v2n bl,n)) bitv')) ``,
	
Cases_on `bitv` >>
Cases_on `bitv'` >>
rw[] >> gvs[] >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
gvs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
);





val bit_range = prove ( ``
! (r:num) .
r > 0 /\
r ≤ 64 ==>
(r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/
r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/
r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/
r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/
r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/
r = 31 \/ r = 32 \/ r = 33 \/ r = 34 \/ r = 35 \/
r = 36 \/ r = 37 \/ r = 38 \/ r = 39 \/ r = 40 \/
r = 41 \/ r = 42 \/ r = 43 \/ r = 44 \/ r = 45 \/
r = 46 \/ r = 47 \/ r = 48 \/ r = 49 \/ r = 50 \/
r = 51 \/ r = 52 \/ r = 53 \/ r = 54 \/ r = 55 \/
r = 56 \/ r = 57 \/ r = 58 \/ r = 59 \/ r = 60 \/
r = 61 \/ r = 62 \/ r = 63 \/ r = 64 )
``,
intLib.COOPER_TAC
);



val bs_width_neg_signed = prove ( ``! r q .
r > 0 /\
r ≤ 64 ==>
r = bs_width (bitv_unop unop_neg_signed (q,r))``,

rpt strip_tac >>
IMP_RES_TAC  bit_range >> fs[] >>
gvs[bitv_unop_def, get_word_unop_def, bs_width_def]

);






val v_typed_bv_op = prove ( ``
! op w bitv bitv' bitv'' b b'.
w ≤ 64 /\ w > 0 /\
is_bv_op (op) /\
bitv_binop op bitv bitv' = SOME bitv'' /\
v_typ (v_bit bitv) (t_tau (tau_bit w)) b /\
v_typ (v_bit bitv') (t_tau (tau_bit w)) b' ==>
v_typ (v_bit bitv'') (t_tau (tau_bit w)) F ``,


     REPEAT STRIP_TAC >>
     FULL_SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
     PairCases_on `bitv` >>
     PairCases_on `bitv'` >>
     PairCases_on `bitv''` >>
     rw[] >>
     rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
     rfs[bitv_binop_def] >>
     IMP_RES_TAC bitv_binop_inner_lemma 
);





(** INDEX_OF theories section **)


(*
 If the property P holds on one list member in index i, then the index is
 indeed within the range of the list
*)
val prop_in_range =
prove(``
 !l P i f. ( INDEX_FIND 0 P l = SOME (i,f)) ==> (i < LENGTH l ) ``,
 REPEAT STRIP_TAC >>
 Cases_on `INDEX_FIND 0 P l = SOME (i,f)` >> 
 fs[] >>
 IMP_RES_TAC index_find_length >>
 fs[]
);



(*
 P should hold on the member it finds.
*)
val P_holds_on_curent = prove(``
  !l P i m. INDEX_FIND i P l = SOME m  ==>
  P (SND m) ``,
  Induct_on `l` >>
  fs[INDEX_FIND_def] >>
  NTAC 2 GEN_TAC >>
  CASE_TAC >>
  rw[]
);





(*
if a property found in some range, then if we started from a previous
index i we should find it.
*)
val P_hold_on_next = prove (``
  !i l P m.  (INDEX_FIND (SUC i) P l = SOME m) =
             (INDEX_FIND i P l = SOME (FST m - 1, SND m) /\ (0 < FST m))``,
Induct_on `l` >>
REPEAT STRIP_TAC >>
EQ_TAC >>
fs[INDEX_FIND_def] >>
rw[] >>
fs[] >>
PairCases_on `m` >>
fs[]
);


(*
if a property holds on some index i starting from 0, then it should hold on the
ith position if starting from 1
*)
val P_implies_next = prove (``
    !l P i m. INDEX_FIND 0 P l = SOME (i, m) ==>
              INDEX_FIND 1 P l = SOME (SUC i, m)
``,
Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >>
fs[] >>
rw[ADD1] >>
fs[Once INDEX_FIND_add] >> (*my new fav thm*)
PairCases_on `z` >>
rw[] >>
fs[INDEX_FIND_def] 
);


(*
if the property holds on some index, starting from
0 or 1 th positions, then the result are the same for for both finds
*)
val P_current_next_same = prove (``
    !l P m n. INDEX_FIND 0 P l = SOME m /\
              INDEX_FIND 1 P l = SOME n ==> SND n = SND m
``,
Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >>
fs[] >>
rw[] >>
fs[Once INDEX_FIND_add] >> 
PairCases_on `z` >>
rw[] >>
fs[INDEX_FIND_def]
);



(*
if we find a property to hold on the ith index, and also we try
to retrive that element using EL, then the reuslt should be the same
*)
val  EL_relation_to_INDEX_lesseq =
prove (``
!l P i m n. INDEX_FIND 0 P l = SOME (i,n) /\ EL i l  = (m) /\
            i <= LENGTH l ==>
            m = n ``,

Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >|[
   fs[Once EL_compute] >>
   rfs[]
   ,
   fs[INDEX_FIND_def] >>
   rw[] >>
   SIMP_TAC arith_ss [Once EL_compute] >>
   CASE_TAC >>
   
   ASSUME_TAC P_hold_on_next >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
   gvs[GSYM ADD1] >> 
   rw[] >>
   IMP_RES_TAC P_holds_on_curent >>
   IMP_RES_TAC index_find_first >>
   rfs[] >>
   rw[] >>
   fs[numeral_pre, PRE_SUB1, PRE_SUC_EQ] >>
   fs[Once INDEX_FIND_add] >> 
   PairCases_on `z` >>
   rw[] >>
   fs[INDEX_FIND_def] >>
     rw[] >>
     RES_TAC >>
     fs[] >>
     rw[] 
]);




(*
same as above, but it holds on strictly less than l
*)
val EL_relation_to_INDEX_less =
prove (``
!l P i m n. INDEX_FIND 0 P l = SOME (i,n) /\
            EL i l  = (m) /\
            i < LENGTH l ==>
            m = n``,
	    
`!l i. i < LENGTH l ==> i <= LENGTH l ` by FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
RES_TAC >>
IMP_RES_TAC EL_relation_to_INDEX_lesseq
 );



(* if P does not hold on any member of list l starting from index 0,
then P does not hold starting from any index n in the list *)
val P_NONE_hold = prove ( ``
!P l n .  (INDEX_FIND 0 P l = NONE) ==> (INDEX_FIND n P l = NONE) `` ,
 Induct_on `l` >>
 REPEAT STRIP_TAC >>
 fs[INDEX_FIND_def] >>
 Cases_on `P h` >>
 fs[] >>
 rw[ADD1] >>
 fs[Once INDEX_FIND_add] 
);



val P_NONE_hold2 = prove ( ``
!P l n .  (INDEX_FIND n P l = NONE) ==> (INDEX_FIND 0 P l = NONE) `` ,
 Induct_on `l` >>
 REPEAT STRIP_TAC >>
 fs[INDEX_FIND_def] >>
 Cases_on `P h` >>
 fs[] >>
 rw[ADD1] >>
 fs[Once INDEX_FIND_add] 
);



val INDEX_FIND_EQ_SOME_0 = store_thm ("INDEX_FIND_EQ_SOME_0",
  ``!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))``,

cheat);





val index_find_concat1 = prove ( ``
! l1 l2 n P.
INDEX_FIND 0 P l1 = NONE  /\
INDEX_FIND 0 P (l2 ⧺ l1) = SOME n ==>
INDEX_FIND 0 P (l2) = SOME n ``,

Induct_on `l1` >>
Induct_on `l2` >>
fs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
CASE_TAC >| [
 rfs[]
 ,
 Cases_on `P h'` >| [
  gvs[]
  ,
  gvs[] >>

  ASSUME_TAC P_hold_on_next>> 
  FIRST_X_ASSUM
  (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`(l2 ⧺ h'::l1)`,`P`,`n`])) >>
  gvs[GSYM ADD1] >> 
  RES_TAC >>
  gvs[] >>

  IMP_RES_TAC P_implies_next >>
  Cases_on `n` >>
  fs[]
  ]
 ]
);




val index_find_concat2 = prove ( ``
! l1 l2 a b P.
INDEX_FIND 0 P l2 = NONE  /\
INDEX_FIND 0 P (l2 ++ l1) = SOME a /\
INDEX_FIND 0 P (l1) = SOME b ==>
(SND a = SND b )

``,

Induct_on `l1` >>
Induct_on `l2` >>
fs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>

Cases_on `P h` >>
fs[] >>

Cases_on `P h'` >>
fs[] >> gvs[] >>

ASSUME_TAC P_hold_on_next >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
gvs[GSYM ADD1] >> rw[] >|[

 (*show that if the property holds on some element,
 then if we append it to a lost, we will find it *)

  subgoal `! i l P h'.
    P h' ==>
    INDEX_FIND i P (h'::l) = SOME (i, h')` >-
    fs[INDEX_FIND_def] >>


 Q.PAT_X_ASSUM ` ∀i l P h'. P h' ⇒ INDEX_FIND i P (h'::l) = SOME (i,h') `
 (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`l1`,`P`,`h'`])) >>
 RES_TAC >>

 Cases_on `a` >>
 fs[] >>

 subgoal `(INDEX_FIND 0 P l2 = NONE)` >-  IMP_RES_TAC P_NONE_hold2 >>

 FIRST_X_ASSUM
 (STRIP_ASSUME_TAC o (Q.SPECL [`h'`,`(q-1,r)`,`(0,h')`,`P`])) >>

 gvs[]  

 ,

 (*Inductive case*)
 (*show that if the property holds on some element,
 then if we append it to a lost, we will find it *)

 subgoal `(INDEX_FIND 0 P l2 = NONE)` >- 
 IMP_RES_TAC P_NONE_hold2 >>

 Cases_on `a` >>
 Cases_on `b` >>
 gvs[] >>

 FIRST_X_ASSUM
 (STRIP_ASSUME_TAC o (Q.SPECL [`h'`,`(q-1,r)`,`(q',r')`,`P`])) >>
 gvs[]
 ]
);








(** EL simplication section **)

val  EL_simp1 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
(q) = EL i (MAP (λ(x_,v_,tau_). (x_)) l) ``,
Induct >>
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_pair_list >>
rw[] >> fs[ELIM_UNCURRY] >>
EVAL_TAC >> METIS_TAC[]
);


val  EL_simp2 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
(r,t) = EL i (MAP (λ(x_,v_,tau_). (v_,tau_)) l) ``,
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_pair_list >>
rw[] >>
fs[ELIM_UNCURRY] >>
METIS_TAC[]
);


val  EL_simp3 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
((r) = EL i (MAP (λ(x_,v_,tau_). (v_)) l) /\
(t) = EL i (MAP (λ(x_,v_,tau_). (tau_)) l)
)``,

REPEAT STRIP_TAC >>
NTAC 2 (
IMP_RES_TAC EL_pair_list >> rw[] >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2) >>
gvs[ELIM_UNCURRY] >>


rfs[EL_pair_list,EL_simp1,EL_simp2] >>
rfs[Once MAP_o] >>
AP_TERM_TAC >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF]
);


val  EL_simp4 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
((q) = EL i (MAP (λ(x_,v_,tau_). (x_)) l) /\
(r) = EL i (MAP (λ(x_,v_,tau_). (v_)) l) /\
(t) = EL i (MAP (λ(x_,v_,tau_). (tau_)) l)) ``,

REPEAT STRIP_TAC >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2 >>
IMP_RES_TAC EL_simp3 
);



val EL_simp5 =
prove (``
!l i q r .
 i<LENGTH l /\
(q,r) = EL i (MAP (λ(x_,v_,tau_). (x_,v_)) l) ==>
((q) = EL i (MAP (λ(x_,v_,tau_). (x_)) l) /\
(r) = EL i (MAP (λ(x_,v_,tau_). (v_)) l) )``,

REPEAT STRIP_TAC >>
rfs[EL_pair_list,EL_simp1,EL_simp2] >>
fs[ELIM_UNCURRY] >>
rfs[] >>
rfs[Once MAP_o] >>
EVAL_TAC >>
AP_TERM_TAC >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
METIS_TAC []
);


val EL_exists1 =
prove (``
!l i q r .
 i<LENGTH l /\
(q,r) = EL i (MAP (λ(x_,v_,tau_). (x_,v_)) l) ==>
?t . (t) = EL i (MAP (λ(x_,v_,tau_). (tau_)) l) ``,
REPEAT STRIP_TAC >>
rfs[EL_pair_list,EL_simp1,EL_simp2] );



val EL_LENGTH_simp = prove ( ``
! l x0 x1 x2 a.
EL (LENGTH l) (MAP (λ(d,x,e). d) l ⧺ [x0]) = x0 ∧
EL (LENGTH l) (MAP (λ(d,x,e). x) l ⧺ [x1]) = x1 ∧
EL (LENGTH l) (MAP (λ(d,x,e). e) l ⧺ [x2]) = x2 ∧
EL (LENGTH l) (l ⧺ [a]) = a 
``,
Induct_on `l` >>
fs[] );



val P_on_any_EL = prove
(``!l i P. i < LENGTH l ==> P (EL i (l)) = EL i (MAP P (l))``,
Induct >> fs[] >> REPEAT STRIP_TAC >>
rw[Once EL_compute] >>
fs[EL_CONS] >>
fs[PRE_SUB1] );



val list_length1 = prove ( ``
! l1 l2 .
LENGTH l1 = SUC (LENGTH l2) ==>
LENGTH (TL l1) = LENGTH l2  ``,
Induct_on `l1` >> Induct_on `l2` >> fs[]
);


(*
Given that we want to find the member that matches with k ,
and given two lists of tuples where the type of the first member
is the same for both lists, then the property should have
the same index for both lists, since we are looking for k in both lists that
are literally the same
*)


val INDEX_FIND_same_list =
prove (``
! l P i i' x x' v r q'.
INDEX_FIND 0 (λ(k,v). k = q') (MAP (λ(x_,v_,tau_). (x_,v_)) l) =
        SOME (i,x,v) /\
INDEX_FIND 0 (λ(k,v). k = q') (MAP (λ(x_,v_,tau_). (x_,tau_)) l) =
        SOME (i',x',r) ==>
	(i = i' /\ r = EL i (MAP (λ(x_,v_,tau_). tau_) l)) ``,


Induct >>
REPEAT GEN_TAC >>
fs[INDEX_FIND_def] >>
CASE_TAC  >>
gvs[] >>
STRIP_TAC >|[
  fs[] >>
  FULL_SIMP_TAC list_ss [] >>
  Cases_on `(λ(k,v). k = q') ((λ(x_,v_,tau_). (x_,tau_)) h)` >>
  fs[] >>
  fs[ELIM_UNCURRY] >>
  rfs[] 
  ,
  fs[] >>
  FULL_SIMP_TAC list_ss [] >>
  Cases_on `(λ(k,v). k = q') ((λ(x_,v_,tau_). (x_,tau_)) h)` >|[
   fs[] >>
   fs[ELIM_UNCURRY]
   ,

   gvs[] >>
   
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#γ)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   				  [`0`, `(MAP (λ(x_,v_,tau_). (x_,tau_)) l)`,
				  `(λ(k,v). k = q')`, `(i',x',r)`])) >>
   gvs[GSYM ADD1] >>

   
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#'b)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   				  [`0`, `(MAP (λ(x_,v_,tau_). (x_,v_)) l)`,
				  `(λ(k,v). k = q')`, `(i,x,v)`])) >>
   gvs[GSYM ADD1] >>
   RES_TAC >>
   `i=i'` by fs[] >>
   rw[] >>
   fs[Once EL_compute] >>
   CASE_TAC >> gvs[] >| [
   `i=1` by fs[] >> rw[]
   ,
   `i>1` by fs[] >> rw[] >>
   gvs[GSYM EL_compute] >>
  fs[EL_CONS] >>
  fs[PRE_SUB1] >>

  rfs[GSYM EL] >>
  gvs[ADD1]
]]]
);



(*
if the field name q has the type tau, and tau is in the list of the
feild types in position i, then it is indeed true that the feild name q
and its type tau can be found in the list (l) at a specific index i
*)
val correct_field_index_lemma = prove (``
! (l:(string#v#tau)list ) i q r tau .
INDEX_FIND 0 (λ(k,v). k = q) (MAP (λ(x_,v_,t_). (x_,v_)) l) =
          SOME (i,EL i (MAP (λ(x_,v_,t_). (x_,v_)) l)) ∧
          correct_field_type (MAP (λ(x_,v_,t_). (x_,t_)) l) q tau ∧
          (q,r) = EL i (MAP (λ(x_,v_,t_). (x_,v_)) l) ⇒
          tau = EL i (MAP (λ(x_,v_,t_). t_) l)``,

REPEAT STRIP_TAC >>
rfs[correct_field_type_def] >>
rfs[tau_in_rec_def] >>
Cases_on `FIND (λ(xm,tm). xm = q) (MAP (λ(x_,v_,t_). (x_,t_)) l)` >>
fs[FIND_def] >>
PairCases_on `z` >>
rw[] >>
Cases_on `SND (z0,z1,z2)` >>
fs[] >>
rw[] >> 

Cases_on `r' = tau` >>
fs[] >>
rw[] >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs[ELIM_UNCURRY] >>
`INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,EL i (MAP (λx. (FST x,FST (SND x))) l)) ==>
INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,q,r)
` by METIS_TAC[] >>
RES_TAC >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs[ELIM_UNCURRY]
);





(*
If INDEX_FIND for some property P finds an element v in list l,
then that element is a member of the list l
*)
val index_mem = prove (``
!l P n v. INDEX_FIND 0 P l = SOME (n,v) ==> MEM v l
``,

Induct >>
fs[] >> rw[] >>
fs[INDEX_FIND_def] >>

Cases_on `P h` >>
fs[] >> rw[] >>

ASSUME_TAC P_hold_on_next>>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`l`,`P`,`(n,v)`])) >>
gvs[GSYM ADD1] >> 
RES_TAC >>
fs[]
);



val index_find_not_mem =
prove (`` ! l P e n. (INDEX_FIND n P l = NONE) /\ P e ==> ~ MEM e l ``,

Induct >>
fs[INDEX_FIND_def] >>
REPEAT GEN_TAC >>
CASE_TAC >>
STRIP_TAC >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`P`, `e` , `SUC n`])) >>
IMP_RES_TAC P_NONE_hold2 >>
Cases_on `e=h` >>
fs[]
);



val mem_fst_snd = prove (``
!l m. MEM m l ==>
      MEM (SND m) (MAP SND l) /\
      MEM (FST m) (MAP FST l) ``,
Induct >>
REPEAT STRIP_TAC >>
fs[]
);




(** REMOVE_LATER SECTION **)
(** REMOVE_LATER SECTION **)

val index_none_not_every =
prove(``! l P n. (( INDEX_FIND n (P) l) = NONE) = (EVERY ($¬ ∘ P) l)``,
cheat
);



(*duplicated from determ proof remove it*)
val ured_mem_length =
prove(`` !l i . (unred_mem_index l = SOME i) ==> i < LENGTH l ``,
 cheat
);

(*this one as well*)
val mem_el_map2 =
prove(`` ! l i .
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (MAP (λ(f_,e_,e'_). e_) l) ==>
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (SND (UNZIP (MAP (λ(f_,e_,e'_). (f_,e_)) l)))	``,

cheat
);

(*this one also dup*)
val lemma_MAP5 =
prove ( ``
!l l' .
        ( MAP (λ(a,b,c). (a,b)) l =
        MAP (λ(a,b,c). (a,b)) l') ==>
	(MAP (λ(a,b,c). (a)) l =
        MAP (λ(a,b,c). (a)) l') /\
	(MAP (λ(a,b,c). (b)) l =
        MAP (λ(a,b,c). (b)) l') ``,

cheat
);




val lemma_v_red_forall = prove ( ``
! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl ``, cheat);




(** MAP theories and simplifications section **)
(** ZIP & UNZIP theorems **)

val lemma_MAP8 =
prove ( ``
! l l' . MAP (λ(a,b,c). (a,b)) l =
         MAP (λ(a,b,c,d). (a,b)) l' ==>
((MAP (λ(a,b,c). (a)) l = MAP (λ(a,b,c,d). (a)) l') /\
(MAP (λ(a,b,c). (b)) l = MAP (λ(a,b,c,d). (b)) l')) `` ,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC >>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
REV_FULL_SIMP_TAC list_ss [] >>
fs[ELIM_UNCURRY]
);



val map_distrub = prove ( 
``!l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>

(MAP (\(a,b,_). a) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a,b,c). b) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a,b,c). c) (ZIP (l,ZIP (l',l''))) = l'' /\
MAP (\(a,b,c). (a,b)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l') /\
MAP (\(a,b,c). (a,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l'') 
)``,
rw[lambda_unzip_tri] >>
rw[lambda_12_unzip_tri] >>
rw[map_tri_zip12] >>
EVAL_TAC >>
fs[GSYM UNZIP_MAP] >>
fs[MAP_ZIP]
);



val map_rw1 = prove ( ``
!l . (MAP (\(a,b,c). (a,c)) l = ZIP (MAP (\(a,b,c). a) l,MAP (\(a,b,c). c) l)) /\
     (MAP (\(a,b,c). (a,b)) l = ZIP (MAP (\(a,b,c). a) l,MAP (\(a,b,c). b) l)) /\
     (MAP (\(a,b,c). (b,c)) l = ZIP (MAP (\(a,b,c). b) l,MAP (\(a,b,c). c) l)) ``,
Induct >>
REPEAT STRIP_TAC >>
fs[GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
);



val map_rw2 = prove ( ``
!l . MAP (\(a,b,c,d). (a,b)) l = ZIP (MAP (\(a,b,c,d). a) l, MAP (\(a,b,c,d). b) l) /\
     MAP (\(a,b,c,d). (a,c)) l = ZIP (MAP (λ(a,b,c,d). a) l, MAP (\(a,b,c,d). c) l) /\
     MAP (\(a,b,c,d). (a,d)) l = ZIP (MAP (λ(a,b,c,d). a) l, MAP (\(a,b,c,d). d) l) /\
     MAP (\(a,b,c,d). (b,c)) l = ZIP (MAP (λ(a,b,c,d). b) l, MAP (\(a,b,c,d). c) l) /\
     MAP (\(a,b,c,d). (b,d)) l = ZIP (MAP (λ(a,b,c,d). b) l, MAP (\(a,b,c,d). d) l) /\
     MAP (\(a,b,c,d). (c,d)) l = ZIP (MAP (λ(a,b,c,d). c) l, MAP (\(a,b,c,d). d) l) 
``,
REPEAT CONJ_TAC >>
Induct >>
REPEAT STRIP_TAC >>
fs[GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
);


val map_simp_1 = prove ( ``! l1 l2.
          MAP SND (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) l1 ) =
          MAP SND (MAP (λ(e_,e'_,x_,d_). (x_,d_)) l2) ==>
	  MAP (λ(e_,e'_,x_,d_). d_) l2=
          MAP (λ(e_,tau_,d_,b_). d_) l1
	  ``,

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
PairCases_on `h'` >>
fs[]
);


val map_simp_2 = prove ( ``! l1 l2.
          l1 = MAP FST (MAP (λ(a,b,c). (b,c)) l2) <=>
	  l1 = MAP (λ(a,b,c). b) l2 
	  ``,

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
);



val map_simp_3 = prove ( ``! l1 l2.
          l1 = MAP FST (MAP (λ(a,b,c,d). (b,c)) l2) <=>
	  l1 = MAP (λ(a,b,c,d). (b)) l2 
	  ``,

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
);


val map_rw_quad = prove ( ``
!l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>
(MAP (\(a,b,c,d). a) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a,b,c,d). b) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a,b,c,d). c) (ZIP (l,ZIP (l',l''))) = FST (UNZIP l'') /\
MAP (\(a,b,c,d). d) (ZIP (l,ZIP (l',l''))) = SND (UNZIP l'') /\
MAP (\(a,b,c,d). (a,b)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l')  /\
MAP (\(a,b,c,d). (a,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l, FST (UNZIP l'') ) /\
MAP (\(a,b,c,d). (b,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l', FST (UNZIP l'') )
)``,

Induct_on `l` >>
Induct_on `l'` >>
Induct_on `l''` >>
rw[lambda_unzip_quad] >>
fs[ELIM_UNCURRY]
);



val mem_triple_map_fst = prove ( ``
! l a b c . MEM (a,b,c) l ==> MEM a (MAP FST l)
``,
Induct_on `l` >>
fs[] >>
REPEAT STRIP_TAC >| [
PairCases_on `h` >>
fs[]
,
RES_TAC >>
fs[]
]
);



val UNZIP_rw = prove(`` !l l'.
(FST (UNZIP (MAP (\(a,b,c). (a,b)) l)) = MAP (\(a,b,c). (a)) l) /\
(FST (UNZIP (MAP (\(a,b,c). (b,c)) l)) = MAP (\(a,b,c). (b)) l) /\
(FST (UNZIP (MAP (\(a,b,c). (a,c)) l)) = MAP (\(a,b,c). (a)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (a,b)) l)) = MAP (\(a,b,c). (b)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (b,c)) l)) = MAP (\(a,b,c). (c)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (a,c)) l)) = MAP (\(a,b,c). (c)) l) /\


(FST (UNZIP (MAP (\(a,b,c,d). (a,b)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (a,c)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (a,d)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (b,c)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (b,d)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (c,d)) l')) = MAP (\(a,b,c,d). (c)) l') /\

(SND (UNZIP (MAP (\(a,b,c,d). (a,b)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (a,c)) l')) = MAP (\(a,b,c,d). (c)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (a,d)) l')) = MAP (\(a,b,c,d). (d)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (b,c)) l')) = MAP (\(a,b,c,d). (c)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (b,d)) l')) = MAP (\(a,b,c,d). (d)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (c,d)) l')) = MAP (\(a,b,c,d). (d)) l') 
``,
Induct_on `l` >>
Induct_on `l'` >>
rw[lambda_unzip_quad] >>
fs[ELIM_UNCURRY]
);


val zipped_list =  prove (``
! (l : ('a # 'b # 'c ) list ) .
 l = (ZIP (MAP (λ(d,x,e). d) l,
      ZIP (MAP (λ(d,x,e). x) l,
            MAP (λ(d,x,e). e) l)))``,

Induct >-
fs[] >>
STRIP_TAC >>
PairCases_on `h` >>
fs[]
);



val EL_ZIP_simp = prove (``
! l a x i.
 i < LENGTH (MAP (λ(x_,v_,t_). (x_,t_)) l) /\
 EL i (MAP (λ(x_,v_,t_). (x_,t_)) l) = (x,a) ==>
 EL i (MAP (λ(x_,v_,t_). t_ ) l) = (a) ``,

Induct >-
fs[Once EL_compute] >>


REPEAT STRIP_TAC >>
fs[Once EL_compute] >>
Cases_on `i=0` >| [
 PairCases_on `h` >>
 fs[]
 ,

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`a`,`x`, `(i:num)-1`])) >>

 gvs[] >>
 fs[numeral_pre, PRE_SUB1, PRE_SUC_EQ ,ADD1] >>
 rw[] >>
 Cases_on `i = 1` >>
 fs[] >>

 `~ (i ≤ 1)` by fs[] >>
 gvs[] >>


 subgoal ` EL (i − 1) (HD ((MAP (λ(x_,v_,t_). (x_,t_)) l))::TL ((MAP (λ(x_,v_,t_). (x_,t_)) l))) =
           EL (PRE (i − 1)) (TL ((MAP (λ(x_,v_,t_). (x_,t_)) l)))  ` >- (
   `0 < i - 1` by fs[] >>
    ASSUME_TAC EL_CONS >>
    Q.PAT_X_ASSUM `∀n. 0 < n ⇒ ∀x l. EL n (x::l) = EL (PRE n) l`
    ( STRIP_ASSUME_TAC o (Q.SPECL [`i-1`])) >>
    RES_TAC >>
    fs[EL_CONS] ) >>

 fs[EL_CONS] >>
 fs[PRE_SUB1] >>
 gvs[] >>

 subgoal ` (HD (MAP (λ(x_,v_,t_). (x_,t_)) l) ::TL (MAP (λ(x_,v_,t_). (x_,t_)) l) ) =
            (MAP (λ(x_,v_,t_). (x_,t_)) l) ` >- (
   `0 < i` by fs[] >>
   `0 < LENGTH l` by fs[] >>
   ` ~(0 >= LENGTH l)` by fs[] >>
   `0 ≥ LENGTH l ⇔ l = []` by fs[quantHeuristicsTheory.LIST_LENGTH_0] >>
   ` ~(l = [])` by fs[] >>
   fs[NULL] >>

   ASSUME_TAC NULL_LENGTH >>
   ASSUME_TAC CONS >>
   RES_TAC >>
   FULL_SIMP_TAC list_ss [CONS, NULL_LENGTH, NULL_DEF, NULL_EQ]
   ) >>

 fs[EL_CONS]
]
);



(******
define an inverse function of vl_of_el 
*)

val el_of_vl_def = Define `
  el_of_vl vl = MAP (\(v). (e_v v)) (vl)
`;



(*
a value list where each member is a constant imples that
the conversion back to an expression list hold
*)
val vl_el_conv = prove( ``
! l l'.  (l = vl_of_el l')  /\ (is_consts l') ==>
         (l' = el_of_vl l) ``,
Induct_on `l` >>
Induct_on `l'` >>
REPEAT STRIP_TAC >>
fs[el_of_vl_def, vl_of_el_def] >>
rw[] >>
Cases_on `h` >>
fs[v_of_e_def, is_const_def, is_consts_def]
);






(** value typing theorems and lemmas **)

(*
if an expression value (e_v v) is well typed,
then that value v is also well typed with the same tau
*)

val ev_types_v = prove (``
! v tau t_scope_list_g t_scope_list T_e .
  e_typ (t_scope_list_g,t_scope_list) T_e (e_v v) (tau) F ==>
  v_typ (v) (tau) F ``,

REPEAT STRIP_TAC >>
OPEN_EXP_TYP_TAC ``e_v v`` >>
fs[] ) ;


(*
if the expression a constant, then the value of that expression
should be able to be typed with the same tau
*)
val e_types_v = prove (``
! v e tau t_scope_list_g t_scope_list T_e .
  is_const(e) /\
  e_typ (t_scope_list_g,t_scope_list) T_e (e) (tau) F ==>
  v_typ ( THE (v_of_e e)) (tau) F ``,

REPEAT STRIP_TAC >>
OPEN_EXP_TYP_TAC ``e`` >>
fs[] >>
fs[v_of_e_def, is_const_def]
) ;



(*
for a list of expressions l',
if all the list members are constants, then accessing any member is a constant
*)
val EL_consts_is_const = prove (``
!l i. i < LENGTH l /\ is_consts (l) ==>
is_const (EL i (l)) `` ,
REPEAT STRIP_TAC >>
fs[is_consts_def] >>
fs[is_const_def] >>
fs[EVERY_EL]
);




(*
if the expression list contains only constant values,
then those values of these expressions 
should be able to be typed with the same tau at the same index of that expression
*)
val evl_types_vl_F = prove(``
!l l' i t_scope_list_g t_scope_list T_e.
(LENGTH l = LENGTH l') /\
(i<LENGTH l) /\
is_consts (l) /\
(e_typ (t_scope_list_g,t_scope_list) T_e
          (EL i l)
          (t_tau (EL i l')) F) ==>
v_typ (EL i (vl_of_el l)) (t_tau (EL i l')) F ``,

Induct_on `l` >>
Induct_on `l'` >>
fs[] >>
REPEAT STRIP_TAC >>

(* first we know that each member of the e list is a constant, via: *)
ASSUME_TAC EL_consts_is_const >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(h'::l): (e list)`, `i`])) >>
fs[] >>
RES_TAC >>

(* simplify the assumptions further to show that
  EL i (h'::l) = e_v v *)
Cases_on `EL i (h'::l)` >>
fs[is_consts_def, is_const_def, EVERY_EL] >>
rw[] >>

(* now we know that the only expression can by typed with such conditions
   is a constant, i.e. (e_v v), thus we can type it with v_typ *)
IMP_RES_TAC e_types_v  >>
gvs[] >>


(* now we should prove the property for both the head and the tail *)
fs[Once EL_compute] >>
CASE_TAC >| [
 (* i=0 *)
 rw[] >>
 fs[vl_of_el_def]
,
 (* i ≠ 0 *)
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`l'`,`(i:num)-1`])) >>
 fs[] >>
 fs[numeral_pre, PRE_SUB1, PRE_SUC_EQ ,ADD1] >>
 rw[] >>
 Cases_on `i = 1` >>
 fs[] >>
 gvs[v_of_e_def] >>
 RES_TAC >>
 gvs[vl_of_el_def] >>

  subgoal ` EL (i − 1) (HD l::TL l) = EL (PRE (i − 1)) (TL l)  ` >- (
  `0 < i - 1` by fs[] >>
  ASSUME_TAC EL_CONS >>
  Q.PAT_X_ASSUM `∀n. 0 < n ⇒ ∀x l. EL n (x::l) = EL (PRE n) l`
  (STRIP_ASSUME_TAC o (Q.SPECL [`i-1`])) >>
  RES_TAC >>
  fs[EL_CONS] ) >>

  subgoal `(HD l::TL l) = l  ` >- (
  `0 < i` by fs[] >>
  `0 < LENGTH l` by fs[] >>
  `~(0 >= LENGTH l)` by fs[] >>
  `0 ≥ LENGTH l ⇔ l = []` by fs[quantHeuristicsTheory.LIST_LENGTH_0] >>
  `~(l = [])` by fs[] >>
  fs[NULL] >>

  ASSUME_TAC NULL_LENGTH >>
  ASSUME_TAC CONS >>
  RES_TAC >>
  FULL_SIMP_TAC list_ss [CONS, NULL_LENGTH, NULL_DEF, NULL_EQ] ) >>

 FIRST_X_ASSUM
 (STRIP_ASSUME_TAC o (Q.SPECL [`t_scope_list_g`, `t_scope_list`, `T_e`])) >>	  
 gvs[] >>
 fs[EL_CONS, PRE_SUB1]
]
);




(*
The constant can never be typed as an lvalue
*)
val value_is_lval = prove ( ``
     ∀v tau t_scope_list_g t_scope_list T_e.
       ~ e_typ (t_scope_list_g,t_scope_list) T_e (e_v v) tau T ``,
fs[Once e_typ_cases] >>
fs[clause_name_def] >>
fs[Once v_typ_cases]
);






(*
given l (expression value list), l' (type list), l'' (lval indication list), where ith element
of l can be typed with ith element of l' and l'', then the can type
the values of the list l, the same exact way using v_typ.
*)
val evl_types_vl_blist = prove ( ``
    ∀l l' l'' i t_scope_list_g t_scope_list T_e.
       LENGTH l = LENGTH l' /\ LENGTH l = LENGTH l'' ∧ i < LENGTH l ∧ is_consts l ∧
       e_typ (t_scope_list_g,t_scope_list) T_e (EL i l) (t_tau (EL i l')) (EL i l'') ⇒
       v_typ (EL i (vl_of_el l)) (t_tau (EL i l')) F ``,

Induct_on `l` >>
Induct_on `l'` >>
Induct_on `l''` >>
fs[] >>

REPEAT STRIP_TAC >> 
(* we already know that this should hold whever v is an not an lval from evl_types_vl_F
   so we need to make cases on the bool representation of the lval, and show that if
   the value is lval, this is incorrect, else use theorem evl_types_vl_F *)

Cases_on `EL i (h::l'')` >>
fs[] >| [

 (*show that this is impossible*)
 IMP_RES_TAC ev_types_v  >>
 ASSUME_TAC EL_consts_is_const >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(h''::l): (e list)`, `i`])) >>
 fs[] >>
 RES_TAC >>

 Cases_on `EL i (h''::l)` >>
 fs[is_consts_def] >>
 fs[is_const_def] >>
 fs[EVERY_EL] >>
 rw[] >>

 Cases_on `v` >>
 OPEN_EXP_TYP_TAC ``(e_v v)`` >>
 gvs[] >>
 OPEN_V_TYP_TAC ``(v)`` >> fs[]
 ,
 IMP_RES_TAC evl_types_vl_F >>
 gvs[]
]
);





(** similar & similarl theorems **)

(* variable name x cannot be looked up in the scope sc if and only if it cannot be looked up
   in the typing scope tc *)
val R_ALOOKUP_NONE_scopes = prove (``
! R v x t sc tc.
 similar R tc sc ==>
((NONE = ALOOKUP sc x)  <=>
(NONE = ALOOKUP tc x ) )``,

Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw[ALOOKUP_MEM] >>

REPEAT STRIP_TAC >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs[similar_def] >>
rw[] >>

LAST_X_ASSUM
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`x`,`tc`])) >>
fs[similar_def,LIST_REL_def]
);




(*
if the variable name is in the scope sc and has the value v , as well as the typing scope tc with the type t , and also we know that tc |- sc, then v : (tau, F)
*)
val R_ALOOKUP_scopes = prove (``
! R v x t sc tc.
( similar R tc sc /\
(SOME v = ALOOKUP sc x)   /\
(SOME t = ALOOKUP tc x ) ) ==>
(R t v)``,

Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw[ALOOKUP_MEM] >>
FULL_SIMP_TAC list_ss [ALOOKUP_def, ALOOKUP_MEM] >>

REPEAT STRIP_TAC >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs[similar_def] >>
rw[] >>

(*lastone*)
Cases_on `h'0 = x` >>
fs[] >>
rw[] >>

LAST_X_ASSUM
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`v`,`x`,`t`, `tc`])) >>
fs[similar_def,LIST_REL_def]
);



val R_find_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = find_topmost_map tcl x)   /\
(SOME l2 = find_topmost_map scl x ) ) ==>
((similar R (SND l1) (SND l2)) /\ (FST l1 = FST l2) )``,


simp [find_topmost_map_def] >>
NTAC 7 STRIP_TAC >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) scl` >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) tcl` >>

fs[] >>
rw[] >>

PairCases_on `l1` >>
PairCases_on `l2` >>

(* first and last subgoal are going to be the same, so use FIRST tactical *)
Cases_on`l10 = l20` >> FIRST [

 (*if the index of both lists are equal show that similarity holds *)

 gvs[] >>

 fs[similarl_def] >>
 IMP_RES_TAC P_holds_on_curent >>
 fs[] >>

 (* we know that the property of INDEX_FIND does now return NONE*)
 Cases_on `ALOOKUP l21 x` >>
 Cases_on `ALOOKUP l11 x` >>
 fs[] >>
 rw[] >>

 (*since the ith element is the same then the relartion R should
 hold in the same index for both*)

 fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
 IMP_RES_TAC LIST_REL_MEM_IMP >>
 IMP_RES_TAC prop_in_range >>
 RES_TAC >>

 (*simplify the scope by using the ith element notaion*)

 subgoal `EL l10 tcl = l11` >- 
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 subgoal `EL l10 scl = l21` >-
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 IMP_RES_TAC R_ALOOKUP_scopes >>
 rw[similar_def]
,

 (*case of index not compatable*)
 (*prove by contradiction*)

 CCONTR_TAC >>
 gvs[] >>


 (*the property holds on both l11 and l21*)
 fs[similarl_def] >>
 IMP_RES_TAC P_holds_on_curent >>
 fs[] >>


 (*simplify all the lookup cases *)
 Cases_on `ALOOKUP l21 x` >>
 Cases_on `ALOOKUP l11 x` >>
 fs[] >>
 rw[] >>


 (*show that the relation holds on both index l20 and l110 for both scl and tcl*)
 fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
 IMP_RES_TAC LIST_REL_MEM_IMP >>
 IMP_RES_TAC prop_in_range >>
 subgoal `similar R (EL l20 tcl) (EL l20 scl) /\ similar R (EL l10 tcl) (EL l10 scl)` >-
 (fs[] >>
 RES_TAC) >>

 (*use this lemma to indicate that if a relation holds on NONE *)
 IMP_RES_TAC R_ALOOKUP_NONE_scopes >>

 subgoal `∀j'. j' < l10 ⇒ ¬(λsc. IS_SOME (ALOOKUP sc x)) (EL j' tcl)` >-
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 subgoal `∀j'. j' < l20 ⇒ ¬(λsc. IS_SOME (ALOOKUP sc x)) (EL j' scl)` >- 
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 subgoal `EL l10 tcl = l11` >-
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 subgoal `EL l20 scl = l21` >-
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

 `l20 < l10 \/ l10 < l20` by fs[] >>

 fs[similar_def,LIST_REL_def] >>
 fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
 IMP_RES_TAC LIST_REL_MEM_IMP >>
 IMP_RES_TAC prop_in_range >>
 RES_TAC >>

 IMP_RES_TAC P_holds_on_curent >>
 RES_TAC >>
 fs[similar_def] >>
 rw[]
,
fs[]
]
);




val R_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = topmost_map tcl x)   /\
(SOME l2 = topmost_map scl x ) ) ==>
(similar R l1 l2)``,

simp [topmost_map_def] >>
REPEAT STRIP_TAC >>

Cases_on `find_topmost_map scl x` >>
Cases_on `find_topmost_map tcl x` >>

fs[] >>
rw[] >>

PairCases_on `x'` >>
PairCases_on `x''` >>
gvs[] >>

ASSUME_TAC R_find_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`R`, `x`, `(x''0,l1)`, `(x'0,l2)`, `scl`, `tcl`])) >>
fs[]
);




val R_lookup_map_scopesl = prove (``
! R v x t scl tcl.
( similarl R tcl scl /\
(SOME v = lookup_map scl x)   /\
(SOME t = lookup_map tcl x ) ) ==>
(R t v)``,

fs[lookup_map_def] >>
REPEAT STRIP_TAC >>

Cases_on `topmost_map tcl x` >>
Cases_on `topmost_map scl x` >>

fs[] >>
rw[] >>

ASSUME_TAC R_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`R`, `x`, `x'`, `x''`, `scl`, `tcl`])) >>

gvs[] >>

Cases_on `ALOOKUP x'' x` >>
Cases_on `ALOOKUP x' x` >>
fs[] >>
rw[] >>

fs[] >>

IMP_RES_TAC  R_ALOOKUP_scopes >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`, `v`])) >>
fs[]
);






val type_scopes_list_LENGTH = prove (``
! l1 l2 . type_scopes_list l1 l2 ==>
          (LENGTH l1 = LENGTH l2)``,

fs[type_scopes_list_def, similarl_def, similar_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC LIST_REL_LENGTH
);


val type_scopes_list_APPEND = prove (``
! l1 l2 l3 l4. type_scopes_list l1 l2 /\
          type_scopes_list l3 l4 ==>
	  type_scopes_list (l1++l3) (l2++l4)``,

fs[type_scopes_list_def, similarl_def, similar_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC LIST_REL_APPEND
);



val varn_is_typed = prove (``
! gsl gtsl sl tsl varn v tau .
          type_scopes_list gsl gtsl ∧
          type_scopes_list sl tsl ∧
          SOME v = lookup_vexp2 sl gsl varn ∧
          SOME tau = lookup_tau tsl gtsl varn ==>
          v_typ v (t_tau tau) F
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>

fs[lookup_vexp2_def] >>
fs[lookup_tau_def] >>

Cases_on `lookup_map (sl ⧺ gsl) varn` >>
Cases_on `lookup_map (tsl ⧺ gtsl) varn` >>
fs[] >> rw[] >>

subgoal `type_scopes_list (sl ⧺ gsl) (tsl ⧺ gtsl)` >-
IMP_RES_TAC type_scopes_list_APPEND >>

PairCases_on `x` >>

fs[type_scopes_list_def] >>
subgoal `∀x v.
          SOME v = lookup_map (sl ⧺ gsl) x ==>
          ∀t. SOME t = lookup_map (tsl ⧺ gtsl) x ==> v_typ (FST v) (t_tau t) F` >-
(IMP_RES_TAC R_lookup_map_scopesl >>
fs[])  >>

Q.PAT_X_ASSUM `∀x v. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`varn`,`(v,x1)`])) >>
gvs[]
);



(*
if var star is not in the domain of the scope s,
then it is not a member of that list
*)
val star_MEM = prove ( ``
!s f.
star_not_in_s (s) ==>  ~MEM (varn_star f) (MAP FST s) ``,

REPEAT STRIP_TAC >>
fs[star_not_in_s_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`f`])) >>
fs[ALOOKUP_NONE]
);



(*
if star is not in any scope of scope lists l, then we should not
find any index and value returned while searching in l's scopes
*)
val star_not_in_s_implies_none = prove ( ``
!l . EVERY (λs. star_not_in_s s) l  ==>
!f . INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (l) = NONE
``,
Induct >>
fs[star_not_in_s_def, INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
RES_TAC >>
fs[P_NONE_hold]
);


val lookup_map_in_gsl_lemma  = prove ( ``
! v lvalop f sl gsl.
SOME (v,lvalop)  = lookup_map (sl ⧺ gsl) (varn_star f) /\
star_not_in_sl sl ==>
SOME (v,lvalop) = lookup_map   gsl (varn_star f)
``,

REPEAT STRIP_TAC >>

fs[star_not_in_sl_def] >>
fs[lookup_vexp2_def] >>
fs[lookup_map_def] >>
fs[topmost_map_def] >>
fs[find_topmost_map_def] >>

Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f)))
                  (sl ⧺ gsl)` >>
rw[] >> fs[] >>

PairCases_on `x` >>
rw[] >> fs[] >>

Cases_on `ALOOKUP x1 (varn_star f)` >>
rw[] >> fs[] >>

PairCases_on `x` >>
rw[] >> fs[] >>

gvs[] >>


Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) gsl` >>
rw[] >> fs[] >>
gvs[] >| [

 IMP_RES_TAC index_find_concat1 >>
 fs[EVERY_MEM] >>
 IMP_RES_TAC index_mem >>
 fs[EVERY_MEM] >>
 RES_TAC >>
 fs[] >>
 IMP_RES_TAC ALOOKUP_MEM >>
 IMP_RES_TAC mem_triple_map_fst >>
 IMP_RES_TAC star_MEM 
 ,
 PairCases_on `x` >>
 fs[] >>
 Cases_on `ALOOKUP x1' (varn_star f)` >>
 rw[] >> fs[] >| [
  IMP_RES_TAC index_find_concat1 >>
  IMP_RES_TAC P_holds_on_curent >>
  gvs[]
  ,
  PairCases_on `x` >>
  fs[] >>
  IMP_RES_TAC star_not_in_s_implies_none>>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`])) >>
  fs[] >>
  IMP_RES_TAC index_find_concat2 >>
  fs[]
  ]
 ]
);





val lookup_in_gsl_lemma = prove ( ``
! v f sl gsl.
SOME v = lookup_vexp2 sl gsl (varn_star f) /\
star_not_in_sl sl ==>
SOME v = lookup_vexp2 [] gsl (varn_star f)   `` ,

REPEAT STRIP_TAC >>
fs[lookup_vexp2_def] >>

Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >> 
Cases_on `lookup_map gsl (varn_star f)` >> fs[] >>
PairCases_on `x` >> fs[] >>

ASSUME_TAC lookup_map_in_gsl_lemma >>
  FIRST_X_ASSUM
  (STRIP_ASSUME_TAC o (Q.SPECL [`v`,`x1`,`f`,`sl`, `gsl`])) >> gvs[]
);








val lookup_map_none_lemma1 = prove ( ``
! t_scope_list_g x .  LENGTH t_scope_list_g = 2 /\
  lookup_map t_scope_list_g (varn_star (funn_name x)) = NONE ==>
  (ALOOKUP (EL 1 t_scope_list_g) (varn_star (funn_name x)) = NONE /\
   ALOOKUP (EL 0 t_scope_list_g) (varn_star (funn_name x)) = NONE)``,

REPEAT STRIP_TAC >>
fs[lookup_map_def] >>
fs[topmost_map_def] >>
fs[find_topmost_map_def] >>

Cases_on `INDEX_FIND 0
(λsc. IS_SOME (ALOOKUP sc (varn_star (funn_name x)))) t_scope_list_g` >>
fs[] >> rw[] >> FIRST[
  (* first and third subgoals *)
  IMP_RES_TAC index_none_not_every >>
  FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
  fs[EVERY_EL] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[]
  ,
  (* second and fourth subgoals *)
  PairCases_on `x'` >>
  fs[] >>
  Cases_on `ALOOKUP x'1 (varn_star (funn_name x))` >>
  fs[] >> rw[] >>
  fs[INDEX_FIND_EQ_SOME_0]
  ]
);





val lookup_glb_local_ctx = prove ( ``

! func_map delta_g func_map delta_b b_func_map s stmt_called
xdl tdl ext_map delta_x tau.

dom_tmap_ei delta_g delta_b /\
dom_g_eq delta_g func_map /\
dom_b_eq delta_b b_func_map /\
SOME (stmt_called,xdl) =
        lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map /\
SOME (tdl,tau) = t_lookup_funn (funn_name s) delta_g delta_b delta_x  ==>

((ALOOKUP func_map s = SOME (stmt_called,xdl) /\
 ALOOKUP delta_g s = SOME (tdl,tau) /\
 (ALOOKUP b_func_map s = NONE /\
 ALOOKUP delta_b s = NONE )) \/
 
(ALOOKUP func_map s = NONE /\
 ALOOKUP delta_g s = NONE /\
ALOOKUP b_func_map s = SOME (stmt_called,xdl) /\
 ALOOKUP delta_b s = SOME (tdl,tau)) 
) ``,

REPEAT STRIP_TAC >>
fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
fs[t_lookup_funn_def] >>
rfs[] >> rw[]  >> 


Cases_on `ALOOKUP b_func_map s` >> 
Cases_on `ALOOKUP delta_b s` >>
fs[] >| [

(*not found in block, so should be global function*)

 Cases_on `ALOOKUP func_map s` >> 
 Cases_on `ALOOKUP delta_g s` >>
 fs[] >> rw[] >>

 PairCases_on `x` >>
 PairCases_on `x'` >>
 rfs[] >>
 RES_TAC >>
 gvs[]
 ,
 (* found b in env but not in typing ctx*)
 rfs[dom_b_eq_def, dom_eq_def] >>
 rfs[is_lookup_defined_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]
 ,
 rfs[dom_b_eq_def, dom_eq_def] >>
 rfs[is_lookup_defined_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]
 ,
 PairCases_on `x` >>
 PairCases_on `x'` >>
 rfs[] >>
 RES_TAC >>
 gvs[] >>


 rfs[dom_g_eq_def, dom_eq_def] >>
 rfs[is_lookup_defined_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[] >>
 
 Cases_on `ALOOKUP func_map s` >> gvs[] >>
 Cases_on `ALOOKUP delta_g s` >> gvs[] >>

 fs[dom_tmap_ei_def] >>
 fs[dom_empty_intersection_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]
 ]
);





val t_lookup_funn_lemma = prove ( ``
! delta_g delta_b delta_x f tdl tau .
SOME (tdl,tau) = t_lookup_funn f delta_g [] [] /\
dom_tmap_ei delta_g delta_b ==>
(? tau' tdl' . ( SOME (tdl',tau') = t_lookup_funn f delta_g delta_b []) /\
               ( SOME (tdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (tdl = tdl' /\ tau = tau'))``,

REPEAT STRIP_TAC >>
Cases_on `f` >>
fs[t_lookup_funn_def] >>


Cases_on `ALOOKUP delta_b s` >>
fs[] >> rw[] >>


Cases_on `ALOOKUP delta_g s` >>
fs[] >> rw[] >>

PairCases_on `x` >>
PairCases_on `x'` >>
fs[] >> rw[] >>


fs[dom_tmap_ei_def] >>
rfs[dom_empty_intersection_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >> gvs[]
);



val t_lookup_funn_blk_lemma = prove ( ``
! delta_g delta_b delta_x f tdl tau .
SOME (tdl,tau) = t_lookup_funn (f) [] delta_b []  ==>
(? tau' tdl' . ( SOME (tdl',tau') = t_lookup_funn f delta_g delta_b []) /\
               ( SOME (tdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (tdl = tdl' /\ tau = tau')) ``,

REPEAT STRIP_TAC >>
Cases_on `f` >>
fs[t_lookup_funn_def] >>
Cases_on `ALOOKUP delta_b s` >>
fs[] >> rw[]
);



val t_lookup_funn_ext_lemma = prove ( ``
! delta_g delta_b delta_x f tdl tau .
SOME (tdl,tau) = t_lookup_funn (f) [] [] delta_x ==>
(? tau' tdl' . ( SOME (tdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (tdl = tdl' /\ tau = tau')) ``,

REPEAT STRIP_TAC >>
Cases_on `f` >>
fs[t_lookup_funn_def]
);







val WT_c_imp_global_or_local_lookup = prove ( ``

! func_map delta_g func_map delta_b b_func_map s stmt_called
xdl ext_map delta_x order t_scope_list_g pars_map tbl_map stmt apply_table_f.
SOME (stmt,xdl) =
        lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map /\
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order t_scope_list_g delta_g delta_b delta_x ==>

((ALOOKUP func_map s = SOME (stmt,xdl) /\
 (? tau tdl . ALOOKUP delta_g s = SOME (tdl,tau)) /\
 (ALOOKUP b_func_map s = NONE /\
 ALOOKUP delta_b s = NONE )) \/
 
(ALOOKUP func_map s = NONE /\
 ALOOKUP delta_g s = NONE /\
ALOOKUP b_func_map s = SOME (stmt,xdl) /\
 (?tau tdl . ALOOKUP delta_b s = SOME (tdl,tau)) 
))
  ``,


REPEAT STRIP_TAC >>
fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
fs[t_lookup_funn_def] >>
rfs[] >> rw[]  >> 


Cases_on `ALOOKUP b_func_map s` >> 
Cases_on `ALOOKUP delta_b s` >>
fs[] >| [

(*not found in block, so should be global function*)

 Cases_on `ALOOKUP func_map s` >> 
 fs[] >> rw[] >>

 PairCases_on `x` >>
 rfs[] >>
 RES_TAC >>
 gvs[] >>

 fs[WT_c_cases, dom_g_eq_def, dom_eq_def] >>
 fs[is_lookup_defined_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >> gvs[] >>
 PairCases_on `y` >> gvs[]
 
 ,
 (* found b in env but not in typing ctx*)


 Cases_on `ALOOKUP func_map s` >> 
 fs[] >> rw[] >>
 PairCases_on `x'` >> gvs[] >>
 fs[WT_c_cases, dom_b_eq_def, dom_eq_def] >>
 fs[is_lookup_defined_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]

 ,
 
 PairCases_on `x` >> gvs[] >>
 fs[WT_c_cases, dom_b_eq_def, dom_eq_def] >>
 fs[is_lookup_defined_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]

 ,
 PairCases_on `x` >>
 PairCases_on `x'` >>
 rfs[] >>
 RES_TAC >>
 gvs[] >>



 fs[WT_c_cases, dom_g_eq_def, dom_eq_def] >>
 fs[is_lookup_defined_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[] >>
 
 Cases_on `ALOOKUP func_map s` >> gvs[] >>
 Cases_on `ALOOKUP delta_g s` >> gvs[] >>

 fs[dom_map_ei_def] >>
  rfs[dom_empty_intersection_def] >>

  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]
 ]
);


val Fg_star_lemma1 = prove ( ``
! t_scope_list_g f func_map delta_g delta_b delta_x order
  b_func_map gscope (ext_map: 'a ext_map)
  stmt xdl apply_table_f pars_map tbl_map .
  
   type_scopes_list gscope t_scope_list_g ∧
   SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map /\
   WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order t_scope_list_g delta_g delta_b delta_x
	  ==>
    ( ? tau tdl. SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x /\
    (SOME tau = find_star_in_globals t_scope_list_g (varn_star f))) ``,

Cases_on `f` >>
REPEAT STRIP_TAC >| [

  (* global and blk functions *)

 IMP_RES_TAC WT_c_imp_global_or_local_lookup >>
 gvs[] >| [

   fs[WT_c_cases] >>
   gvs[WTFg_cases, func_map_typed_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`stmt`, `xdl`, `s`])) >>
   gvs[] >>
   IMP_RES_TAC t_lookup_funn_lemma >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`])) >>
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,
   fs[WT_c_cases] >>
   gvs[WTFb_cases, func_map_blk_typed_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`stmt`, `xdl`, `s`])) >> gvs[] >>
   IMP_RES_TAC t_lookup_funn_blk_lemma >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`, `delta_g`])) >>
   srw_tac [SatisfySimps.SATISFY_ss][]
   ]
 ,

 fs[lookup_funn_sig_body_def] >>
 Cases_on `ALOOKUP ext_map s` >> gvs[] >>
 PairCases_on `x` >> gvs[] >>
 Cases_on `x0` >> gvs[] >>
 PairCases_on `x` >> gvs[] >>
 

 fs[WT_c_cases] >>
 gvs[WTX_cases, extern_map_IoE_typed_def] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`x0`, `s`, `x1'`, `x1`])) >> gvs[] >>
  
 IMP_RES_TAC t_lookup_funn_ext_lemma >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_g`,`delta_b`])) >>
 srw_tac [SatisfySimps.SATISFY_ss][]

,


 fs[lookup_funn_sig_body_def] >>
 Cases_on `ALOOKUP ext_map s` >> gvs[] >>
 PairCases_on `x` >> gvs[] >>
 Cases_on `ALOOKUP x1 s0` >> gvs[] >>
 PairCases_on `x` >> gvs[] >>
 

 fs[WT_c_cases] >>
 gvs[WTX_cases, extern_MoE_typed_def] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`x0'`, `s`, `s0`, `x0`, `x1`, `x1'`])) >> gvs[] >>
  
 IMP_RES_TAC t_lookup_funn_ext_lemma >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`delta_g`,`delta_b`])) >>
 srw_tac [SatisfySimps.SATISFY_ss][]
]
);







val Fg_star_lemma2 = prove ( ``
! t_scope_list_g f func_map tau delta_g delta_b delta_x order
b_func_map gscope (ext_map: 'a ext_map) tau tdl
  stmt xdl apply_table_f pars_map tbl_map .
  
   type_scopes_list gscope t_scope_list_g ∧
   
   SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map /\
   
   WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
         order t_scope_list_g delta_g delta_b delta_x /\
	 SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x ==>
    (? tau' . SOME tau' = find_star_in_globals t_scope_list_g (varn_star f) /\
                   tau = tau' ) ``,
REPEAT STRIP_TAC >>
IMP_RES_TAC Fg_star_lemma1 >>
gvs[] >>
Cases_on `t_lookup_funn f delta_g delta_b delta_x` >> rfs[] >>
PairCases_on `x` >> gvs[]
);




val e_resulted_frame_is_WT = prove ( ``
! (c:'a ctx) gscope scopest e e' f_called stmt_called copied_in_scope
  t_scope_list_g t_scope_list order delta_g delta_b delta_x delta_t f Prs_n (ty:'a itself) b tau.
    e_red c gscope scopest e e' [(f_called,[stmt_called],copied_in_scope)] /\
    sr_exp e ty /\
    type_scopes_list gscope t_scope_list_g /\
    type_scopes_list scopest t_scope_list /\
    star_not_in_sl scopest /\
    e_typ (t_scope_list_g,t_scope_list) (order,f,delta_g,delta_b,delta_x,delta_t) e (tau) b /\
    WT_c c order t_scope_list_g delta_g delta_b delta_x 
    ==>
    ∃t_scope_list_fr. frame_typ (t_scope_list_g,t_scope_list_fr)
            (order,f_called,delta_g,delta_b,delta_x,delta_t) Prs_n gscope copied_in_scope
            [stmt_called] ``,

REPEAT STRIP_TAC >>
gvs[] >>

Q.PAT_X_ASSUM `sr_exp e ty`
((STRIP_ASSUME_TAC o (Q.SPECL
[`e'`, `gscope`, `scopest`, `[(f_called,[stmt_called],copied_in_scope)]`, `t_scope_list`,
`t_scope_list_g`, `tau`, `b`, `c`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f`])) o
SIMP_RULE (srw_ss()) [sr_exp_def]) >>

gvs[] 
);



val lookup_funn_t_map_NONE = prove (``
! delta_g delta_b delta_x func_map b_func_map ext_map f .
dom_tmap_ei delta_g delta_b /\
dom_g_eq delta_g func_map /\
dom_b_eq delta_b b_func_map /\
dom_x_eq delta_x ext_map  ==>
(t_lookup_funn (f) delta_g delta_b delta_x = NONE <=>
lookup_funn_sig_body (f) func_map b_func_map ext_map = NONE) ``,

REPEAT STRIP_TAC >>
fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
fs[t_lookup_funn_def] >>
rfs[] >> rw[]  >> 

Cases_on `f` >> gvs[]  >| [

 Cases_on `ALOOKUP b_func_map s` >> 
 Cases_on `ALOOKUP delta_b s` >>
 fs[] >>

 TRY (PairCases_on `x`) >>
 TRY(PairCases_on `x'`) >>
 rfs[] >>

 (*not found in block, so should be global function*)

 Cases_on `ALOOKUP func_map s` >> 
 Cases_on `ALOOKUP delta_g s` >> 
 fs[] >> rw[] >>


 TRY (PairCases_on `x`) >>
 TRY (PairCases_on `x'`) >>
 rfs[] >>
 
 fs[dom_g_eq_def, dom_eq_def] >>
 fs[dom_b_eq_def, dom_eq_def] >>
 fs[is_lookup_defined_def] >>
 REPEAT (
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[])
 ,

 (* fun_inst*)

 Cases_on `ALOOKUP delta_x s` >> 
 Cases_on `ALOOKUP ext_map s` >>
 fs[] >>

 TRY (PairCases_on `x`) >>
 TRY (PairCases_on `x'`) >>

 rfs[dom_x_eq_def, dom_eq_def] >> gvs[] >>
 fs[is_lookup_defined_def] >>
 REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
         gvs[])  >>
 
 Cases_on `x0` >>
 Cases_on `x'0` >>
 gvs[] >>


 PairCases_on `x` >>
 PairCases_on `x'` >>
 gvs[]
 ,
 
 Cases_on `ALOOKUP delta_x s` >> 
 Cases_on `ALOOKUP ext_map s` >>
 fs[] >>

 TRY (PairCases_on `x`) >>
 TRY (PairCases_on `x'`) >>
 rfs[] >>

  rfs[dom_x_eq_def, dom_eq_def] >> gvs[] >>
  fs[is_lookup_defined_def] >| [
   
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
            gvs[])
   ,
 
   REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
            gvs[]) 
 
   ,
   
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
   gvs[]  >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`s0`])) >>
   gvs[] >>


   Cases_on `ALOOKUP x1 s0` >>
   Cases_on `ALOOKUP x'1 s0` >>
   gvs[] >>

   TRY (PairCases_on `x`) >>
   TRY (PairCases_on `x'`) >>
   rfs[] 
 ]
]
);








val tfunn_imp_sig_body_lookup = prove ( ``
! apply_table_f ext_map func_map b_func_map pars_map tbl_map
  order t_scope_list_g delta_g delta_b delta_x tdl tau f.
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
       order t_scope_list_g delta_g delta_b delta_x /\
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x  ==>
?stmt xdl.
    SOME (stmt,xdl) =
    lookup_funn_sig_body f func_map b_func_map ext_map ∧
    MAP SND tdl = MAP SND xdl ∧
    LENGTH (MAP SND xdl) = LENGTH (MAP SND tdl) ∧
    ALL_DISTINCT (MAP FST xdl)
``,

fs[WT_c_cases] >>
REPEAT STRIP_TAC >>
 Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >> gvs[] >| [

   (* show that this is impossible *)
   ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a``] lookup_funn_t_map_NONE) >>
   RES_TAC >>
   gvs[] 
   ,

   Cases_on `f` >| [
   
     PairCases_on `x` >> gvs[] >>
     ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a``] lookup_glb_local_ctx) >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`func_map`, `delta_g`, ` func_map`, ` delta_b`, ` b_func_map`, ` s`, `x0`,
      ` x1`, ` tdl`, `ext_map`, ` delta_x`, `tau`])) >> gvs[] >| [

     fs[WTFg_cases] >>
     fs[func_map_typed_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`,`x1`, `s`])) >>
     gvs[] >>

     ASSUME_TAC t_lookup_funn_lemma >> RES_TAC >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`])) >>
     Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >>
     gvs[] >>
     METIS_TAC[GSYM LENGTH_MAP] 
     ,
     fs[WTFb_cases] >>
     fs[func_map_blk_typed_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`,`x1`, `s`])) >>
     gvs[] >>

     IMP_RES_TAC t_lookup_funn_blk_lemma >> RES_TAC >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`,`delta_g`])) >>
     Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >> gvs[] >>
     METIS_TAC[GSYM LENGTH_MAP] 
     ]
     
   ,
   (* extern object instansiation *)

   fs[WTX_cases] >>
   fs[extern_map_IoE_typed_def] >>

   fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
   fs[t_lookup_funn_def] >>

   Cases_on `ALOOKUP ext_map s` >>
   Cases_on `ALOOKUP delta_x s` >>
   fs[] >> rw[] >>

   PairCases_on `x''` >> PairCases_on `x'` >> gvs[] >>
   Cases_on `x'0` >> Cases_on `x''0` >> gvs[] >>
   Cases_on `x''` >> Cases_on `x'` >> gvs[] >>

   RES_TAC >> gvs[] >>
   METIS_TAC[GSYM LENGTH_MAP] 
   ,
   (* extern object methods *)

   fs[WTX_cases] >>
   fs[extern_MoE_typed_def] >>

   fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
   fs[t_lookup_funn_def] >>

   Cases_on `ALOOKUP ext_map s` >>
   Cases_on `ALOOKUP delta_x s` >>
   fs[] >> rw[] >>

   PairCases_on `x''` >>
   PairCases_on `x'` >>
   gvs[] >>
   Cases_on `ALOOKUP x'1 s0` >>
   Cases_on `ALOOKUP x''1 s0` >>
   gvs[] >>
   PairCases_on `x''` >>
   PairCases_on `x'` >>
   gvs[] >>
   RES_TAC >> gvs[] >>
   METIS_TAC[GSYM LENGTH_MAP]
   ]
 ]);








val tfunn_imp_sig_lookup = prove ( ``
! apply_table_f ext_map func_map b_func_map pars_map tbl_map
  order t_scope_list_g delta_g delta_b delta_x tdl tau f.
    WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order t_scope_list_g delta_g delta_b delta_x /\
    SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x ==>
            ? xdl.
            SOME xdl = lookup_funn_sig f func_map b_func_map ext_map /\
            MAP SND tdl = MAP SND xdl /\
            LENGTH (MAP SND xdl) = LENGTH (MAP SND tdl) /\
            ALL_DISTINCT (MAP FST xdl)  
``,

REPEAT STRIP_TAC >>
fs[lookup_funn_sig_def] >>
Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >>
fs[] >| [

 ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a``] lookup_funn_t_map_NONE) >> 
 fs[WT_c_cases] >> gvs[] >> RES_TAC >>
 srw_tac [] [] >>
 Cases_on `t_lookup_funn f delta_g delta_b delta_x ` >>
 fs[]
 ,

 PairCases_on `x` >>
 gvs[] >>

 IMP_RES_TAC tfunn_imp_sig_body_lookup >>
 gvs[]
]
);









val out_is_val_imp_every = prove (``
 ! dl bl .
   out_is_lval dl bl ==>
   EVERY (\ (dir,b) . is_d_out dir ==> b ) (ZIP(dl, bl))``,

fs[out_is_lval_def] >>
fs[EVERY_EL] >>
Induct_on `bl` >>
Induct_on `dl` >>
gvs[] >>
REPEAT STRIP_TAC >>
Cases_on `n` >| [

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
 fs[EL_CONS]
 ,
 fs[EL_CONS] >>
 fs[PRE_SUB1] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`dl`])) >>

  subgoal `! i . is_d_out (EL i (dl)) ⇒ EL i (bl)` >-
  ( STRIP_TAC >>
    Q.PAT_X_ASSUM `∀i. is_d_out (EL i (h::dl)) ⇒ EL i (h'::bl)`
    (STRIP_ASSUME_TAC o (Q.SPECL [`i+1`])) >>
    fs[EL_CONS] >>
    fs[PRE_SUB1] 
  ) >>
  RES_TAC
  ]
);



val dir_list_lemma1 = prove ( ``
! dl bl i.
i < LENGTH dl /\
out_is_lval dl bl /\
(~is_d_out (EL i dl)) ==>
! b . out_is_lval dl (LUPDATE b i bl) ``,

fs[out_is_lval_def] >>
Induct_on `bl` >>
Induct_on `dl` >>
gvs[] >>
REPEAT STRIP_TAC >| [
 Cases_on `i` >>

 fs[Once EL_restricted] >>
 rfs[EVERY_DEF] >>
 fs[] >>
 rw[LUPDATE_def]
 ,
 Cases_on `i' = i` >>
 gvs[] >>
 SRW_TAC [] [EL_LUPDATE] 
]
);




val unred_arg_index_details = prove ( ``
! dl el i .
 unred_arg_index dl el = SOME i ⇒
          ((EL i dl = d_in ∨ EL i dl = d_none) ∧ ¬is_const (EL i el)) ∨
          ((EL i dl = d_inout ∨ EL i dl = d_out) ∧ ¬is_e_lval (EL i el))``,

Induct_on `dl` >>
Induct_on `el` >>

fs[unred_arg_index_def] >>
REPEAT STRIP_TAC >>
fs[find_unred_arg_def] >>
fs[INDEX_FIND_def] >| [
   (* first two subgoals *)
 Cases_on `INDEX_FIND 0 (λ(d,e). ¬is_arg_red d e) (ZIP ([],h::el))` >>
 fs[] >>
 PairCases_on `x` >>
 fs[] >>
 rw[] >>
 fs[INDEX_FIND_EQ_SOME_0]
 ,
 Cases_on `INDEX_FIND 0 (λ(d,e). ¬is_arg_red d e) (ZIP (h::dl,[]))` >>
 fs[] >>
 PairCases_on `x` >>
 fs[] >>
 rw[] >>
 fs[INDEX_FIND_EQ_SOME_0]
 ,
 fs[] >>
 Cases_on `¬is_arg_red h' h` >>
 fs[] >| [
  
  (* i = 0 *)
  fs[is_arg_red_def] >>
  Cases_on `h'` >>
  fs[is_d_out_def]
  ,
  Cases_on `INDEX_FIND 1 (λ(d,e). ¬is_arg_red d e) (ZIP (dl,el))` >>
  fs[] >>
  PairCases_on `x` >>
  fs[] >>

  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(d#e)``] P_hold_on_next)  >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`,
                                             `(ZIP (dl,el))` ,
                                             `(λ(d,e). ¬is_arg_red d e)` ,
					     `(x0,x1,x2)`])) >>
  gvs[GSYM ADD1] >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`el`, `i-1`])) >>

  Cases_on `INDEX_FIND 0 (λ(d,e). ¬is_arg_red d e) (ZIP (dl,el))` >>
  fs[] >>

  PairCases_on `x` >>
  Cases_on `i = 0` >>
  fs[] >>
  gvs[] >>
  fs[EL_CONS, PRE_SUB1]
  ]
]
);




val unred_arg_index_result = prove ( ``
! dl el i .
unred_arg_index dl el = SOME i ⇒
       ¬is_d_out (EL i dl) ∧ ¬is_const (EL i el) ∨
       is_d_out (EL i dl) ∧ ¬is_e_lval (EL i el)``,

NTAC 4 STRIP_TAC >> 
IMP_RES_TAC unred_arg_index_details >>
SRW_TAC [] [unred_arg_index_details, is_d_out_def] 
);



val unred_arg_out_is_lval_imp = prove ( ``
∀i dl bl el.
unred_arg_index dl el = SOME i ∧ out_is_lval dl bl ⇒
            EL i bl ∨ EL i dl = d_none ∨ EL i dl = d_in ``,	    
REPEAT STRIP_TAC >>
IMP_RES_TAC unred_arg_index_details>>
fs[out_is_lval_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
fs[is_d_out_def] >>
RES_TAC
);




(* simplify using above function *)
val dir_fun_delta_same = prove ( ``
! xdl tdl ftau f func_map b_func_map ext_map delta_g delta_b delta_x
apply_table_f order t_scope_list_g pars_map tbl_map . 
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order t_scope_list_g delta_g delta_b delta_x /\
SOME (xdl) = lookup_funn_sig f func_map b_func_map ext_map /\
SOME (tdl, ftau) = t_lookup_funn f delta_g delta_b delta_x  ==>
MAP SND tdl = MAP SND xdl ``,

REPEAT STRIP_TAC  >>
IMP_RES_TAC tfunn_imp_sig_lookup >>
gvs[] >>
Cases_on `lookup_funn_sig f func_map b_func_map ext_map` >> rfs[]
);







val two_lookup_funn = prove ( ``
! f delta_g delta_b delta_x tau tau' tdl tdl'.
SOME (tdl,tau) = t_lookup_funn (f) delta_g delta_b delta_x /\
SOME (tdl',tau') = t_lookup_funn (f) delta_g delta_b delta_x ==>
	(tau = tau') /\ (tdl= tdl') ``,

REPEAT STRIP_TAC >>
Cases_on `t_lookup_funn f delta_g delta_b delta_x` >> gvs[]
);





val e_lval_tlval = prove ( ``
!e b t_scope_list t_scope_list_g order f delta_g delta_b delta_x delta_t tau gscope scopest.
 type_scopes_list gscope t_scope_list_g /\
 type_scopes_list scopest t_scope_list  /\
e_typ (t_scope_list_g,t_scope_list)
          (order,f,delta_g,delta_b,delta_x,delta_t) e tau b
	  ==> b ==> is_e_lval (e)
``,

Induct >> 

REPEAT STRIP_TAC >~ [`is_e_lval (e_acc e s)`] >-
(
OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
fs[] >>
SIMP_TAC list_ss [is_e_lval_def, get_lval_of_e_def] >>
Cases_on `get_lval_of_e e` >>
fs[] >> rw[] >>
`is_e_lval e` by RES_TAC >>
FULL_SIMP_TAC list_ss [is_e_lval_def, get_lval_of_e_def] >>
gvs[]
)

>~ [`is_e_lval (e_slice e e' e'')`] >-

(
OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >>
fs[] >>
SIMP_TAC list_ss [is_e_lval_def, get_lval_of_e_def] >>
fs[] >> rw[] >>
`is_e_lval e` by RES_TAC >>
FULL_SIMP_TAC list_ss [is_e_lval_def, get_lval_of_e_def] >>
gvs[] >>
Cases_on `get_lval_of_e e` >>
gvs[]

) >>


fs[is_e_lval_def, get_lval_of_e_def] >>
fs[Once e_typ_cases] >>
fs[is_e_lval_def, get_lval_of_e_def] >>
fs[Once v_typ_cases] 
);




(** context related theorems **)






(*
if the expression can be typed using only the global functions typing context,
then it should be also typed with any other block, and extern typuying contexts.
*)

val fg_e_typ_def = Define `
   fg_e_typ (e:e) (ty:'a itself)  =
   (! s tau b order t_scope_list_g t_scope_local delta_g delta_b delta_x delta_t .
dom_tmap_ei delta_g delta_b /\
e_typ (t_scope_list_g,t_scope_local)
          (order,funn_name s,delta_g,[],[],[]) e tau b
==>
e_typ (t_scope_list_g,t_scope_local)
          (order,funn_name s,delta_g,delta_b,delta_x,delta_t) e tau b )
`;



val fg_el_typ_def = Define `
   fg_el_typ (el:e list) (ty:'a itself)  =
    ! e . MEM e el ==> fg_e_typ (e:e) (ty:'a itself)
`;


val fg_stel_typ_def = Define `
   fg_stel_typ (stel: (string#e) list ) (ty:'a itself)  =
    ! e . MEM e (SND (UNZIP stel)) ==> fg_e_typ (e:e) (ty:'a itself)
`;



val fg_stetup_typ_def = Define `
   fg_stetup_typ (stetup: (string#e)) (ty:'a itself)  =
      fg_e_typ (SND stetup) ty
`;





val fg_e_typed_tac = TRY( OPEN_EXP_TYP_TAC ``(e)``) >>
                 SIMP_TAC list_ss [Once e_typ_cases] >>
                 gvs[] >>
                 RES_TAC >>
		 IMP_RES_TAC t_lookup_funn_lemma >>
                 srw_tac [SatisfySimps.SATISFY_ss][] >>
		 METIS_TAC[]



val fg_exp_typed_thm = prove (  ``
 ! (ty:'a itself) . (
(! e  . fg_e_typ (e) ty) /\
(! el . fg_el_typ (el) ty) /\
(! stel . fg_stel_typ (stel) ty) /\
(! stetup . fg_stetup_typ (stetup) ty))
``,

STRIP_TAC >>
Induct >>
fs[fg_e_typ_def] >>
REPEAT STRIP_TAC >>

 FIRST [
  (* resolves the : f call*)

   OPEN_EXP_TYP_TAC ``(e_call f l)`` >>
   SIMP_TAC list_ss [Once e_typ_cases] >>
   gvs[] >>
   RES_TAC >>
   Q.EXISTS_TAC `e_tau_d_b_list` >>
   gvs[] >>

   CONJ_TAC >| [
     rw[] >>
     IMP_RES_TAC t_lookup_funn_lemma >>
     srw_tac [SatisfySimps.SATISFY_ss][] >>
     gvs[]
     ,

     REPEAT STRIP_TAC >>
     fs[fg_el_typ_def, fg_e_typ_def] >>
     RES_TAC >>

     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`EL i (MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list: (e # tau # d # bool) list))`])) >>
     fs[MEM_EL] >>

     RES_TAC >>
     gvs[ELIM_UNCURRY]
     ]
 ,

 (* resolves the : struct, header*)

 fs[fg_stel_typ_def, fg_e_typ_def] >>
 OPEN_EXP_TYP_TAC ``(e_struct stel)`` >>
 SIMP_TAC list_ss [Once e_typ_cases] >>
 gvs[] >>
 RES_TAC >>
 Q.EXISTS_TAC `f_e_tau_b_list` >>
 gvs[] >>

 REPEAT STRIP_TAC >>
 RES_TAC >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`EL i (MAP (λ(f_,e_,tau_,b_). e_) (f_e_tau_b_list: (string # e # tau # bool) list))`])) >>
 fs[MEM_EL] >>

  subgoal `! l i . EL i (MAP (λx. FST (SND x)) l) =
                   EL i (SND (UNZIP (MAP (λx. (FST x,FST (SND x))) l)))` >-
   (Induct >>
    FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
    REPEAT STRIP_TAC >>
    PairCases_on `h` >>
    Cases_on `i'` >>
    fs[] ) >>

 RES_TAC >>
 SRW_TAC [] [] >>
 gvs[ELIM_UNCURRY, UNZIP_rw]
 ,

 (* resolves the : v, var, e_list, acc e s, unop, binop, concat, slice, select*)
 
 fg_e_typed_tac
 ,

 (* resolves the : inductive cases on the properties *)
 fs[fg_e_typ_def, fg_el_typ_def, fg_stel_typ_def, fg_stetup_typ_def] >>
 REPEAT STRIP_TAC >>
 gvs[]
]
);








(*
if the expression can be typed using the global, block local, and x functions typing context,
then it should be also typed with tables typing contexts.
*)
val fb_e_typ_def = Define `
   fb_e_typ (e:e) (ty:'a itself)  =
   (! s tau b order t_scope_list_g t_scope_local delta_g delta_b delta_x delta_t .
dom_tmap_ei delta_g delta_b /\
e_typ (t_scope_list_g,t_scope_local)
          (order,funn_name s,delta_g,delta_b,delta_x,[]) e tau b
==>
e_typ (t_scope_list_g,t_scope_local)
          (order,funn_name s,delta_g,delta_b,delta_x,delta_t) e tau b )
`;



val fb_el_typ_def = Define `
   fb_el_typ (el:e list) (ty:'a itself)  =
    ! e . MEM e el ==> fb_e_typ (e:e) (ty:'a itself)
`;


val fb_stel_typ_def = Define `
   fb_stel_typ (stel: (string#e) list ) (ty:'a itself)  =
    ! e . MEM e (SND (UNZIP stel)) ==> fb_e_typ (e:e) (ty:'a itself)
`;



val fb_stetup_typ_def = Define `
   fb_stetup_typ (stetup: (string#e)) (ty:'a itself)  =
      fb_e_typ (SND stetup) ty
`;





val fb_e_typed_tac = TRY( OPEN_EXP_TYP_TAC ``(e)``) >>
                 SIMP_TAC list_ss [Once e_typ_cases] >>
                 gvs[] >>
                 RES_TAC >>
		 IMP_RES_TAC t_lookup_funn_lemma >>
                 srw_tac [SatisfySimps.SATISFY_ss][] >>
		 METIS_TAC[]



val fb_exp_typed_thm = prove (  ``
 ! (ty:'a itself) . (
(! e  . fb_e_typ (e) ty) /\
(! el . fb_el_typ (el) ty) /\
(! stel . fb_stel_typ (stel) ty) /\
(! stetup . fb_stetup_typ (stetup) ty))
``,

STRIP_TAC >>
Induct >>
fs[fb_e_typ_def] >>
REPEAT STRIP_TAC >>

FIRST [


(* resolves the : f call*)

OPEN_EXP_TYP_TAC ``(e_call f l)`` >>
SIMP_TAC list_ss [Once e_typ_cases] >>
gvs[] >>
RES_TAC >>
Q.EXISTS_TAC `e_tau_d_b_list` >>
gvs[] >>

 REPEAT STRIP_TAC >>
 fs[fb_el_typ_def, fb_e_typ_def] >>
 RES_TAC >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`EL i (MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list: (e # tau # d # bool) list ) ) `])) >>
 fs[MEM_EL] >>

 RES_TAC >>
 gvs[ELIM_UNCURRY]

,

(* resolves the : struct, header*)

fs[fb_stel_typ_def, fb_e_typ_def] >>
OPEN_EXP_TYP_TAC ``(e_struct stel)`` >>
SIMP_TAC list_ss [Once e_typ_cases] >>
gvs[] >>
RES_TAC >>
Q.EXISTS_TAC `f_e_tau_b_list` >>
gvs[] >>

REPEAT STRIP_TAC >>
RES_TAC >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`EL i (MAP (λ(f_,e_,tau_,b_). e_) (f_e_tau_b_list: (string # e # tau # bool) list ) ) `
])) >>
fs[MEM_EL] >>

subgoal `! l i . EL i (MAP (λx. FST (SND x)) l) =
        EL i (SND (UNZIP (MAP (λx. (FST x,FST (SND x))) l)))` >-
(Induct >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
Cases_on `i'` >>
fs[] ) >>

RES_TAC >>
SRW_TAC [] [] >>
gvs[ELIM_UNCURRY, UNZIP_rw]
,

(* resolves the : v, var, e_list, acc e s, unop, binop, concat, slice, select*)

fb_e_typed_tac

,

(* resolves the : inductive cases on the properties *)
fs[fb_e_typ_def, fb_el_typ_def, fb_stel_typ_def, fb_stetup_typ_def] >>
REPEAT STRIP_TAC >>
gvs[]
]
);




val trans_names_imp = prove ( ``
! l Prs_n . 
literials_in_P_state l ["accept"; "reject"] ==>
literials_in_P_state l (Prs_n ⧺ ["accept"; "reject"]) ``,

fs[literials_in_P_state_def] >>
Induct >>
fs[]
);





val fg_stmt_typ_theorm =  prove (``
! stmt c f' order t_scope_list_g t_scope_list_g s delta_g delta_b
  delta_x delta_t Prs_n order t_scope_local ty.
      dom_tmap_ei delta_g delta_b ∧
      ordered (funn_name s) f' order ∧
      stmt_typ (t_scope_list_g,t_scope_local)
               (order,funn_name s,delta_g,[],[],[]) [] stmt ⇒
      stmt_typ (t_scope_list_g,t_scope_local)
               (order,funn_name s,delta_g,delta_b,delta_x,delta_t) Prs_n stmt	  
``,

Induct >>
REPEAT STRIP_TAC >> 

(* this should resolve most cases *)
OPEN_STMT_TYP_TAC ``stmt`` >>
SIMP_TAC list_ss [Once stmt_typ_cases] >>
fs[] >>
ASSUME_TAC fg_exp_typed_thm >>
fs[fg_e_typ_def]  >>
RES_TAC >>
srw_tac [SatisfySimps.SATISFY_ss][]

(* two cases left which are return and trans *) 
>|[
 Q.EXISTS_TAC `tau_d_list` >>
 Q.EXISTS_TAC `tau` >>
 Q.EXISTS_TAC `b` >>
 IMP_RES_TAC t_lookup_funn_lemma >>
 srw_tac [SatisfySimps.SATISFY_ss][] >>
 gvs[]
 ,
 Q.EXISTS_TAC `x_list` >>
 Q.EXISTS_TAC `b` >>
 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][] >>
 gvs[trans_names_imp]
]
);




val fb_stmt_typ_theorm =  prove (``
! stmt c f' order t_scope_list_g t_scope_list_g s delta_g delta_b
  delta_x delta_t Prs_n order t_scope_local ty.
      dom_tmap_ei delta_g delta_b ∧
      ordered (funn_name s) f' order ∧
      stmt_typ (t_scope_list_g,t_scope_local)
               (order,funn_name s,delta_g,delta_b,delta_x,[]) [] stmt ⇒
      stmt_typ (t_scope_list_g,t_scope_local)
               (order,funn_name s,delta_g,delta_b,delta_x,delta_t) Prs_n stmt	  
``,

Induct >>
REPEAT STRIP_TAC >> 

(* this should resolve most cases *)
OPEN_STMT_TYP_TAC ``stmt`` >>
SIMP_TAC list_ss [Once stmt_typ_cases] >>
fs[] >>
ASSUME_TAC fb_exp_typed_thm >>
fs[fb_e_typ_def]  >>
RES_TAC >>
srw_tac [SatisfySimps.SATISFY_ss][] >>

(* one case left which are return and trans *) 

Q.EXISTS_TAC `x_list` >>
Q.EXISTS_TAC `b` >>
gvs[] >>
srw_tac [SatisfySimps.SATISFY_ss][] >>
gvs[trans_names_imp]

);






(*we need to show that the statement that we get is always extern
  the scope is well typed and it is always well typed*)

val funn_inst_ext_prod_ext_stmt = prove ( ``
! f s s' stmt xdl func_map b_func_map ext_map .
(f = funn_inst s \/ f = (funn_ext s s')) /\
SOME (stmt,xdl) = lookup_funn_sig_body (f) func_map b_func_map ext_map ==>
stmt= stmt_ext
``,

REPEAT STRIP_TAC >>
gvs[] >>
fs[lookup_funn_sig_body_def] >>
Cases_on `ALOOKUP ext_map s` >>
rfs[] >>
rw[] >>

PairCases_on `x` >>
Cases_on `x0` >>
fs[] >>
rw[] >>

Cases_on `ALOOKUP x1 s'` >>
gvs[] >>

PairCases_on `x` >>
TRY (PairCases_on `x'`) >>
gvs[]
);










val all_func_maps_contains_welltyped_body = prove ( ``

! xdl tdl stmt tau f f'
  apply_table_f ext_map func_map b_func_map pars_map tbl_map
  order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n .
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order t_scope_list_g delta_g delta_b delta_x /\
MAP SND tdl = MAP SND xdl /\
ordered f f' order /\
LENGTH tdl = LENGTH xdl /\
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x /\	
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map ==>

stmt_typ (t_scope_list_g, [ZIP (mk_varn (MAP FST xdl), MAP FST tdl)])
          (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n stmt
``,

fs[WT_c_cases] >>
REPEAT STRIP_TAC >>

Cases_on `f` >| [
 (* funn name s *)

 drule (INST_TYPE [``:'b`` |-> ``:'a``] lookup_glb_local_ctx) >> 
 STRIP_TAC >>
 gvs[] >>
     
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`func_map`, ` b_func_map`, ` s`, ` stmt`, ` xdl`,
   ` tdl`, `ext_map`, ` delta_x`, ` tau`])) >>
 gvs[] >| [
   (* global functions *)
   gvs[] >>
   fs[WTFg_cases] >>
   fs[func_map_typed_def] >>

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`,`xdl `,`s`])) >>
   gvs[UNZIP_rw] >>


     subgoal `tdl' = tdl` >- (
       IMP_RES_TAC t_lookup_funn_lemma >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`])) >>
       gvs[] >>
       Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >>
       gvs[]) >>
     srw_tac [] [fg_stmt_typ_theorm] >>

     drule (INST_TYPE [``:'b`` |-> ``:funn list``] fg_stmt_typ_theorm) >> 
     gvs[] >>
     STRIP_TAC >>
     RES_TAC >>
     srw_tac [] []
     ,
      (* block local *)
     gvs[] >>
     fs[WTFb_cases] >>
     fs[func_map_blk_typed_def] >>

     LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`,`xdl `,`s`])) >>
     gvs[UNZIP_rw] >>


       subgoal `tdl' = tdl` >- (
         IMP_RES_TAC t_lookup_funn_blk_lemma >>
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`, `delta_g`])) >>
	 gvs[] >>
	 Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >>
	 gvs[]) >>
     srw_tac [] [fb_stmt_typ_theorm] >>

     drule (INST_TYPE [``:'b`` |-> ``:funn list``] fb_stmt_typ_theorm) >> 
     gvs[] >>
     STRIP_TAC >>
     RES_TAC >>
     srw_tac [] []
  ]
 ,
         (* funn inst s *)
 IMP_RES_TAC funn_inst_ext_prod_ext_stmt >>
 srw_tac [SatisfySimps.SATISFY_ss] [Once stmt_typ_cases, clause_name_def]
 ,
        (* funn ext s s' *)
 IMP_RES_TAC funn_inst_ext_prod_ext_stmt >>
 srw_tac [SatisfySimps.SATISFY_ss] [Once stmt_typ_cases, clause_name_def]
]
);









(** copyin abstraction theorems **)


val copyin_abstract_def = Define `
  copyin_abstract xlist dlist elist (ss:scope list) (scope:scope) =
((! i. ( i < LENGTH xlist)==>
(IS_SOME(one_arg_val_for_newscope (EL i dlist) (EL i elist) ss) /\
EL i scope =
(varn_name (EL i xlist) , THE (one_arg_val_for_newscope (EL i dlist) (EL i elist) ss) )
/\
LENGTH scope = LENGTH xlist)) /\
((LENGTH xlist = 0) ==> scope = []))
`;


val wf_arg_def = Define `
wf_arg d x e ss =
 ((~is_d_out d ==> ?v. v_of_e e = SOME v) /\
  (is_d_out d  ==> ?lval v. get_lval_of_e e = SOME lval /\ lookup_lval ss lval = SOME v))
`;



val wf_arg_list_def = Define `
wf_arg_list dlist (xlist: string list) elist ss =
       !i . ((LENGTH xlist > 0 /\ i < LENGTH xlist) ==>
          wf_arg (EL i dlist) (EL i xlist) (EL i elist) ss) \/
            (LENGTH xlist = 0 /\ LENGTH dlist = 0 /\ LENGTH elist = 0)
        `;



val WF_arg_empty = prove ( ``
!ss d x e.
   wf_arg d x e ss ⇒
    update_arg_for_newscope ss (SOME []) (d,x,e) =
    SOME [(varn_name x,THE (one_arg_val_for_newscope d e ss))]
``,
  
fs[wf_arg_def] >>
REPEAT STRIP_TAC >>
Cases_on `d` >>
fs[is_d_out_def] >>

fs[update_arg_for_newscope_def,
one_arg_val_for_newscope_def] >>
fs[is_d_out_def, is_d_in_def] >>
fs[AUPDATE_def]
);



val update_args_none = prove ( ``
! dxel scope ss.
~ (FOLDL (update_arg_for_newscope ss) NONE (dxel) = SOME scope)
``,

Induct_on `dxel` >>
fs[update_arg_for_newscope_def] >>
REPEAT GEN_TAC >>
PairCases_on `h` >>
EVAL_TAC >>
gvs[]
);




val wf_arg_normalization = prove (``
! d dl x xl e el ss.
wf_arg_list (d::dl) (x::xl) (e::el) ss ==>
wf_arg d x e ss /\ wf_arg_list (dl) (xl) (el) ss ``,

REPEAT STRIP_TAC >>
fs[wf_arg_list_def] >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`0`])) >>
 fs[wf_arg_def] 
 ,
 STRIP_TAC >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i+1`])) >>
 fs[wf_arg_def] >>
 gvs[] >>
 fs[EL_CONS] >>
 fs[PRE_SUB1]
 ]
);





val wf_arg_list_normalization_imp1 = prove ( ``
! dxel d x e ss .
(wf_arg_list (MAP (λ(d,x,e). d) dxel) (MAP (λ(d,x,e). x) dxel)
          (MAP (λ(d,x,e). e) dxel) ss /\
 wf_arg_list [d] [x] [e] ss) ==>
(wf_arg_list (MAP (λ(d,x,e). d) dxel ⧺ [d])
              (MAP (λ(d,x,e). x) dxel ⧺ [x])
	      (MAP (λ(d,x,e). e) dxel ⧺ [e]) ss ) ``,

SIMP_TAC list_ss [wf_arg_list_def] >>
REPEAT STRIP_TAC >>
Cases_on `dxel = []` >| [
 gvs[]
 ,
 INST_FST [`0`] >>
 INST_FST [`i`] >>

 Cases_on `LENGTH dxel = i` >| [
   gvs[] >>
   rfs[EL_LENGTH_simp] 
   ,
   gvs[] >>
   NTAC 3  (rfs[Once EL_APPEND1,LENGTH_MAP])
  ]
]
);




val wf_arg_list_normalization_imp2 = prove (``
! xl dl el x d e ss .
(LENGTH dl = LENGTH xl) /\
(LENGTH el = LENGTH xl) /\
wf_arg_list (dl ++ [d]) (xl ++ [x]) (el ++ [e]) ss ==>
((wf_arg_list (dl) (xl) (el) ss) /\
 wf_arg d x e ss ) ``,

Induct_on `dl` >>
Induct_on `xl` >>
Induct_on `el` >>
fs[] >>
REPEAT STRIP_TAC >| [
 fs[wf_arg_list_def]
 ,

 fs[wf_arg_list_def] >>
 INST_FST [`0`] >>
 gvs[]
 ,

 IMP_RES_TAC wf_arg_normalization >>
 gvs[] >>
 RES_TAC >>
 gvs[] >>

 SIMP_TAC list_ss [wf_arg_list_def] >>
 REPEAT STRIP_TAC >>
 SIMP_TAC list_ss [Once EL_compute] >>
 CASE_TAC >>

 gvs[EL_CONS] >>
 `i>0` by fs[] >>

 fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ] >>

 Q.PAT_X_ASSUM `wf_arg_list dl xl el ss`
 ( STRIP_ASSUME_TAC o (Q.SPECL [`i-1`]) o SIMP_RULE (srw_ss()) [wf_arg_list_def] ) >>

 `LENGTH xl > 0` by fs[] >>
 `i < LENGTH xl + 1` by fs[] >>
 gvs[]
 ,

 IMP_RES_TAC wf_arg_normalization >>
 gvs[] >>
 RES_TAC >>
 gvs[] 
]
);






val wf_arg_none_single = prove ( ``
! ss d s e .
 wf_arg d s e ss ==> 
   ~ (update_arg_for_newscope ss (SOME []) (d,s,e) = NONE )
``,

fs[wf_arg_def, update_arg_for_newscope_def, one_arg_val_for_newscope_def] >>
REPEAT STRIP_TAC >>
Cases_on `is_d_out d` >| [
 fs[] >>

 Cases_on `get_lval_of_e e` >>
 fs[] >> rw[] >>

 Cases_on `lookup_lval ss lval` >>
 fs[] >> rw[] >>

 Cases_on `is_d_in d` >>
 fs[is_d_in_def, is_d_out_def] >> rw[] 
 ,
 fs[] >>

 Cases_on `v_of_e e` >>
 fs[] >> rw[] 
 ]
);




val wf_imp_val_lval = prove ( ``
! ss d s e .
 wf_arg d s e ss ==> 
  ? v lval_op . one_arg_val_for_newscope d e ss = SOME (v , lval_op)  ``,

fs[wf_arg_def, one_arg_val_for_newscope_def] >>
REPEAT STRIP_TAC >>
Cases_on `is_d_out d` >| [
fs[] >>

Cases_on `get_lval_of_e e` >>
fs[] >> rw[] >>

Cases_on `lookup_lval ss lval` >>
fs[] >> rw[] >>

Cases_on `is_d_in d` >>
fs[is_d_in_def, is_d_out_def] >> rw[] 
,
fs[] >>

Cases_on `v_of_e e` >>
fs[] >> rw[] 
] );





val EL_domain_ci_same = prove ( ``
! dxel scope ss i.
i<LENGTH scope /\
LENGTH scope = LENGTH dxel /\
copyin_abstract (MAP (λ(d,x,e). x) dxel)
                (MAP (λ(d,x,e). d) dxel)
	        (MAP (λ(d,x,e). e) dxel) ss scope ==>
   FST (EL i scope) = (varn_name (EL i (MAP (λ(d,x,e). x) dxel)) ) ``,
SIMP_TAC list_ss [copyin_abstract_def]
);




val wf_arg_list_NONE = prove ( ``
       ! dxel x d e ss.
       ALL_DISTINCT (MAP (λ(d,x,e). x) dxel )  /\
       (wf_arg_list (MAP (λ(d,x,e). d) dxel )
                    (MAP (λ(d,x,e). x) dxel )
		    (MAP (λ(d,x,e). e) dxel ) ss) ==>
      ~ (FOLDL (update_arg_for_newscope ss) (SOME []) dxel = NONE) ``,

 HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC]  >>
 fs[SNOC_APPEND] >>
 PairCases_on `x` >>
 fs[] >>

 `ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
 IMP_RES_TAC wf_arg_list_normalization_imp2 >>
 gvs[] >>
 RES_TAC >>
 Cases_on `FOLDL (update_arg_for_newscope ss) (SOME []) dxel` >>
 fs[] >>

 SIMP_TAC list_ss [update_arg_for_newscope_def] >>
 IMP_RES_TAC wf_imp_val_lval >>
 gvs[]
);
 



val args_ci_scope_LENGTH = prove ( ``
! dxel ss scope.
copyin_abstract (MAP (λ(d,x,e). x) (dxel))
                (MAP (λ(d,x,e). d) (dxel))
		(MAP (λ(d,x,e). e) (dxel)) ss scope ==>
		(LENGTH scope = LENGTH dxel)  ``,
Induct >>
REPEAT STRIP_TAC >>
fs[copyin_abstract_def] >>
INST_FST [`0`] >>
fs[]
);



val args_ci_scope_LENGTH2 = prove ( ``
! xl dl el ss scope.
LENGTH xl = LENGTH dl /\ LENGTH xl = LENGTH el /\
copyin_abstract (xl) (dl) (el) ss scope ==>
		(LENGTH scope = LENGTH xl)  ``,
Induct >>
REPEAT STRIP_TAC >>
fs[copyin_abstract_def] >>
INST_FST [`0`] >>
fs[]
);


val LOOKUP_LENGTH = prove ( ``
! l a x . ALOOKUP l a = SOME x ==> ~(LENGTH l = 0) ``,
Induct >>
fs[]);



val LOOKUP_EXISTS_EL = prove ( ``
! l x a .
LENGTH l > 0 /\
ALOOKUP l x = SOME a ==>
? i . ( i < LENGTH l /\ (EL i l = (x,a))) ``,

Induct >- fs[] >>
REPEAT STRIP_TAC >>
Cases_on `h` >>
fs[ALOOKUP_def] >>
Cases_on `q=x` >| [
 fs[] >>
 Q.EXISTS_TAC `0` >>
 rw[Once EL_compute]
 ,
 INST_FST [`x`, `a`] >>
 gvs[] >>
 IMP_RES_TAC LOOKUP_LENGTH >>
 gvs[] >>
 subgoal `LENGTH l > 0 ` >- (Induct_on `l` >> fs[]) >>
 fs[] >>
 
 Q.EXISTS_TAC `i+1` >>
 rw[Once EL_compute] >>
 fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ]
]   
);   





val copyin_abstract_normalize_tmp = prove ( ``
! xl dl el  x d e ss scope.
LENGTH xl = LENGTH dl /\
LENGTH xl = LENGTH el /\
copyin_abstract (x::xl)
          (d::dl) (e::el) ss scope
==>
(copyin_abstract [x] [d] [e] ss [HD scope] /\
          copyin_abstract xl dl el ss (TL scope)) ``,

Induct_on `xl` >>
Induct_on `el` >>
Induct_on `dl` >>
fs[] >| [
 fs[copyin_abstract_def] >>
 REPEAT STRIP_TAC  >| [
   `i=0` by fs[] >>
   fs[] >>
   INST_FST [`0`] >> fs[]
   ,
   INST_FST [`0`] >> fs[] >>
   Cases_on `scope` >> fs[]
 ]
 ,

 REPEAT STRIP_TAC >| [

   fs[copyin_abstract_def] >>
   NTAC 2 STRIP_TAC >>
   `i=0` by fs[] >>
   fs[] >>
   INST_FST [`0`]
   ,

   gvs[] >>

   IMP_RES_TAC args_ci_scope_LENGTH2 >> fs[] >> gvs[] >>
   Cases_on `scope = []` >>
   fs[] >>

   SIMP_TAC list_ss [copyin_abstract_def] >>
   NTAC 2 STRIP_TAC >>

   fs[Once EL_compute] >>
   CASE_TAC >>
        fs[EL_CONS] >>
     fs[copyin_abstract_def] >| [

     INST_FST [`1`] >> fs[] >>
   
     Cases_on `one_arg_val_for_newscope h0 h2 ss` >> fs[] >>
     Cases_on `scope` >> fs[]
     ,

     `i>0` by fs[] >>
     INST_FST [`i+1`] >>

     `i + 1 < LENGTH xl +2` by fs[] >>  

     fs[EL_CONS] >>

     fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ] >>


     fs[Once EL_compute] >>
     Cases_on `i = 0` >> fs[] >>
     Cases_on `i = 1` >> fs[] >> 
     fs[EL_CONS] >>
     Cases_on `scope` >> fs[] >>
   
     fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ] >>
     fs[EL_CONS] >>

     fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ]
     ]
  ]
]);




(* simplify it later, it works without the induction*)
val copyin_abstract_normalize = prove ( ``
! dxel x d e ss scope. 
copyin_abstract (x::MAP (λ(d,x,e). x) (dxel))
                (d::MAP (λ(d,x,e). d) (dxel))
		(e::MAP (λ(d,x,e). e) (dxel)) ss scope  ==>
   (copyin_abstract [x] [d] [e] ss ([HD scope]) /\
    copyin_abstract (MAP (λ(d,x,e). x) (dxel))
          (MAP (λ(d,x,e). d) (dxel)) (MAP (λ(d,x,e). e) (dxel)) ss (TL scope))``,
Induct >>
REPEAT STRIP_TAC >| [

 fs[copyin_abstract_def] >>
 NTAC 2 STRIP_TAC >>
 `i=0` by fs[] >>
 fs[] >>
 INST_FST [`0`]
 ,
 fs[copyin_abstract_def] >>
 INST_FST [`0`] >>
 Cases_on `scope` >> fs[]
 ,
 PairCases_on `h` >>
 fs[] >>
 fs[copyin_abstract_def] >>
 NTAC 2 STRIP_TAC >>
 `i=0` by fs[] >>
 fs[] >>
 INST_FST [`0`]
 ,
 PairCases_on `h` >>
 fs[] >>
 
 IMP_RES_TAC args_ci_scope_LENGTH2 >> fs[] >>
 Cases_on `scope = []` >>
 fs[] >>

 SIMP_TAC list_ss [copyin_abstract_def] >>
 NTAC 2 STRIP_TAC >>

 fs[Once EL_compute] >>
 CASE_TAC >| [

   fs[EL_CONS] >>
   fs[copyin_abstract_def] >>

   INST_FST [`1`] >>

   Cases_on `one_arg_val_for_newscope h0 h2 ss` >> fs[] >>
   Cases_on `scope` >> fs[]
   ,

   fs[EL_CONS] >>
   `i>0` by fs[] >>

   fs[copyin_abstract_def] >>

   INST_FST [`i+1`] >> fs[] >>
   `i + 1 < LENGTH dxel +2` by fs[] >>

   fs[EL_CONS] >>
   fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ] >>


   fs[Once EL_compute] >>
   Cases_on `i = 0` >> fs[] >>
   Cases_on `i = 1` >> fs[] >> 
   fs[EL_CONS] >>
   Cases_on `scope` >> fs[] >>

   fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ] >>
   fs[EL_CONS] >>
   fs[numeral_pre,PRE_SUB1,PRE_SUC_EQ]
   ]
]
);




val copyin_abstract_single = prove (``
! x d e ss scope .
copyin_abstract [x] [d] [e] ss [HD scope] ==>
(ALL_DISTINCT (MAP FST [HD scope]) /\
 FST (HD scope) = varn_name x)
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC args_ci_scope_LENGTH2 >>
fs[copyin_abstract_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`0`])) >> fs[]
);



val mk_varn_lemma = prove (``
! xl s. ~ MEM (s) xl ==>
        ~ MEM (varn_name s) (mk_varn (xl))
``,
Induct >> fs[mk_varn_def] );


val mk_varn_lemma2 = prove (``
!l h. mk_varn (h::l) = (varn_name h)::mk_varn l
``,
Induct_on `l` >> fs[mk_varn_def] );



val copyin_abstract_domain = prove ( ``
! dxel ss  scope.
copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
          (MAP (λ(d,x,e). e) dxel) ss scope ==>
           MAP FST scope = mk_varn (MAP (λ(d,x,e). x) dxel)
``,
Induct >-
fs[copyin_abstract_def, mk_varn_def] >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
fs[] >>

IMP_RES_TAC copyin_abstract_normalize >>
fs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`ss`, `TL (scope : (varn # v # lval option) list)`])) >> gvs[] >>

IMP_RES_TAC copyin_abstract_single >>
fs[mk_varn_lemma2] >>
Cases_on `scope` >> fs[mk_varn_def, copyin_abstract_def]
);



val mk_varn_lemma3 = prove ( ``
! xl . 
ALL_DISTINCT (xl) ==>
ALL_DISTINCT (mk_varn (xl)) ``,

Induct >- fs[mk_varn_def] >>
REPEAT STRIP_TAC >>
gvs[mk_varn_lemma, mk_varn_lemma2]
);




(* if all the domain is distict, then if we find something in there,
it should notmbe as the tail of it *)
val copyin_abstract_distinct =  prove (``
! dxel ss x.
 ALL_DISTINCT (MAP (λ(d,x,e). x) dxel) /\
 copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel) ss x ==>
ALL_DISTINCT (MAP FST x)	  
``,
REPEAT STRIP_TAC >>

IMP_RES_TAC copyin_abstract_domain >>
`ALL_DISTINCT (MAP FST x) = ALL_DISTINCT (mk_varn (MAP (λ(d,x,e). x) dxel))` by fs[] >>
rw[] >>
gvs[mk_varn_lemma3]
);




val copyin_deter_single = prove ( ``
! h h' x d e ss .
copyin_abstract [x] [d] [e] ss [h'] /\
copyin_abstract [x] [d] [e] ss [h] ==>
(h' = h) ``,

fs[copyin_abstract_def] >>
REPEAT STRIP_TAC  >>
INST_FST [`0`] >>
INST_FST [`0`] >>
gvs[]
);




val copyin_abstract_distinct_app =  prove (``
! dxel ss x a.
ALL_DISTINCT ((MAP (λ(d,x,e). x) dxel) ++ [a] )/\
 copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel) ss x ==>
 ALL_DISTINCT ((MAP FST x) ++ [varn_name a] )
``,
REPEAT STRIP_TAC >>
fs[ALL_DISTINCT_APPEND] >>
IMP_RES_TAC copyin_abstract_domain >>
`ALL_DISTINCT (MAP FST x) = ALL_DISTINCT (mk_varn (MAP (λ(d,x,e). x) dxel))` by fs[] >>
gvs[mk_varn_lemma3, mk_varn_lemma]
);


val distinct_not_neg =  prove (``
! l xl x v lval_op x'.
LENGTH l = LENGTH xl /\
ALOOKUP l (varn_name x) = SOME x' /\
EL (LENGTH xl) (l ⧺ [(varn_name x,v,lval_op)]) = (varn_name x,v,lval_op) /\
ALL_DISTINCT (MAP FST l ⧺ [varn_name x]) ==>
~ALL_DISTINCT (MAP FST l ⧺ [varn_name x]) ``,

Induct_on `l` >>
Induct_on `xl` >>
fs[] >>

REPEAT STRIP_TAC >>
PairCases_on `x'` >>
PairCases_on `h'` >>
gvs[] >>
Cases_on `h'0 = varn_name x` >> fs[] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`xl`, `x`, `v`, `lval_op`, `(x'0,x'1)`])) >>
gvs[] 
);



val distinct_not_neg_in_bound =  prove (``
! l x x'.
ALOOKUP l (varn_name x) = SOME x' /\
ALL_DISTINCT (MAP FST l ⧺ [varn_name x])
==>
F ``,
Induct_on `l` >>
fs[] >>
REPEAT STRIP_TAC >>

PairCases_on `h` >>
Cases_on `h0 = varn_name x` >> fs[]
);






val copyin_last_calculate = prove (``
! dxel x scope ss x0 x1 x2 v lval_op .  
copyin_abstract (MAP (λ(d,x,e). x) dxel ⧺ [x1])
                (MAP (λ(d,x,e). d) dxel ⧺ [x0])
		(MAP (λ(d,x,e). e) dxel ⧺ [x2]) ss scope /\
copyin_abstract (MAP (λ(d,x,e). x) dxel)
		(MAP (λ(d,x,e). d) dxel)
		(MAP (λ(d,x,e). e) dxel) ss x /\
one_arg_val_for_newscope x0 x2 ss = SOME (v,lval_op) /\
LENGTH x = LENGTH dxel
==>
scope = (x ++ [(varn_name x1,v,lval_op)]) ``,


Induct >>
REPEAT STRIP_TAC >| [

 fs[copyin_abstract_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`0`])) >>
 gvs[] >>
 Cases_on `scope` >> fs[]
 ,

 PairCases_on `h` >> fs[] >>

 IMP_RES_TAC copyin_abstract_normalize >>
 IMP_RES_TAC copyin_abstract_normalize_tmp >> fs[] >>
 gvs[] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`TL x`, `TL scope` , `ss`, `x0`, `x1`,`x2`])) >> gvs[] >>


 IMP_RES_TAC copyin_abstract_single >>
 IMP_RES_TAC args_ci_scope_LENGTH >>
 gvs[] >>

 Cases_on `scope` >>
 Cases_on `x` >> gvs[] >>

 IMP_RES_TAC copyin_deter_single >> gvs[]
]
);




val copyin_abstract_verbose = prove (``
! dxel ss scope.
     (ALL_DISTINCT (MAP (\(d,x,e).x) dxel)) ∧
     ( wf_arg_list
        (MAP (\(d,x,e).d) dxel)
	(MAP (\(d,x,e).x) dxel)
	(MAP (\(d,x,e).e) dxel) ss) ==>
         ( (FOLDL (update_arg_for_newscope ss) (SOME []) dxel) =
      SOME scope ⇔
      copyin_abstract (MAP (\(d,x,e).x) dxel) (MAP (\(d,x,e).d) dxel) (MAP (\(d,x,e).e) dxel) ss scope) ``,



HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC]  >-
fs[copyin_abstract_def] >>
fs[SNOC_APPEND] >>
PairCases_on `x` >>
fs[] >>

SIMP_TAC list_ss [update_arg_for_newscope_def] >>
Cases_on `FOLDL (update_arg_for_newscope ss) (SOME []) dxel` >>
fs[] >| [

  (* first show that all disttic means that the list and the element is also distict *)
  (* case ¬copyin_abstract *)
  
 `ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
 `ALL_DISTINCT [x1]` by fs[ALL_DISTINCT_APPEND] >>

 IMP_RES_TAC wf_arg_list_normalization_imp2 >>
 gvs[] >>
 fs[wf_arg_list_NONE]
 ,
 
 `ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
 `ALL_DISTINCT [x1]` by fs[ALL_DISTINCT_APPEND] >>
 IMP_RES_TAC wf_arg_list_normalization_imp2 >> gvs[] >>

 (*case of copy in abstract as a list *)

 RES_TAC >>
 IMP_RES_TAC wf_imp_val_lval >> fs[] >>
 EQ_TAC >>
 STRIP_TAC >| [
 
   (* first side of the implication AUPDATE ==> copyin_abstract *)
   SIMP_TAC list_ss [copyin_abstract_def] >>
   NTAC 2 STRIP_TAC >>
   Cases_on `i = (LENGTH dxel) ` >| [

     (*i = LENGTH dxel case*)

     rfs[] >>
     rfs[EL_LENGTH_simp] >>
     gvs[] >>
     IMP_RES_TAC args_ci_scope_LENGTH >>
     fs[AUPDATE_def] >>

     Cases_on `ALOOKUP x (varn_name x1)` >| [

       (*Cases lookup is NONE *)
       fs[] >>
       `EL (LENGTH x) (x ⧺ [(varn_name x1,v,lval_op)]) =
       (varn_name x1,v,lval_op) ` by fs[EL_LENGTH_simp] >>
       gvs[]
       ,
       fs[] >>
       `EL (LENGTH x) (x ⧺ [(varn_name x1,v,lval_op)]) =
       (varn_name x1,v,lval_op) ` by fs[EL_LENGTH_simp] >>
       gvs[] >>
       IMP_RES_TAC copyin_abstract_distinct_app >>
       IMP_RES_TAC distinct_not_neg
       ]
   ,

   (* i ≠ LENGTH dxel /\ i < LENGTH dxel case*)
 
   (* This should not be true at all, since we start
   from a distict xlist we should end up in a distict
   scope, which means that we can never find the variable *)  
    
   fs[] >>
   `i < LENGTH dxel` by fs[] >>

   (* sould stay here, because we extract the definition
   of copyin_abstract in the next step, we cannot infer it later *)
   IMP_RES_TAC copyin_abstract_distinct_app >>

   fs[copyin_abstract_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`i`])) >>  


   `IS_SOME (one_arg_val_for_newscope (EL i (MAP (λ(d,x,e). d) dxel))
             (EL i (MAP (λ(d,x,e). e) dxel)) ss)` by RES_TAC >>
   `EL i x =
        (varn_name (EL i (MAP (λ(d,x,e). x) dxel)),
         THE
           (one_arg_val_for_newscope (EL i (MAP (λ(d,x,e). d) dxel))
              (EL i (MAP (λ(d,x,e). e) dxel)) ss))` by RES_TAC >>
   `LENGTH x = LENGTH dxel` by RES_TAC >>


   (* show that the element is i in the list  *)

   `((EL i (MAP (λ(d,x,e). e) dxel) = EL i (MAP (λ(d,x,e). e) dxel ⧺ [x2])))
   ` by FULL_SIMP_TAC list_ss [EL_APPEND1] >>

   `((EL i (MAP (λ(d,x,e). d) dxel) = EL i (MAP (λ(d,x,e). d) dxel ⧺ [x0])))
   ` by FULL_SIMP_TAC list_ss [Once EL_APPEND1] >>

   `((EL i (MAP (λ(d,x,e). x) dxel) = EL i (MAP (λ(d,x,e). x) dxel ⧺ [x1])))
   ` by FULL_SIMP_TAC list_ss [Once EL_APPEND1] >>


   Cases_on `one_arg_val_for_newscope (EL i (MAP (λ(d,x,e). d) dxel ⧺ [x0]))
             (EL i (MAP (λ(d,x,e). e) dxel ⧺ [x2])) ss` >> fs[] >>
   rfs[] >>

   gvs[] >>
   fs[AUPDATE_def] >>

   Cases_on `ALOOKUP x (varn_name x1)` >>
   fs[] >|[

     FULL_SIMP_TAC list_ss [] >>

     subgoal ` (varn_name (EL i (MAP (λ(d,x,e). x) dxel ⧺ [x1])),x') = EL i x` >-
     (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`i`])) >> fs[] >> gvs[]) >>

      (*
      trivial now!!
      we should show that :
      (EL i x eq EL i (x ⧺ [(varn_name x1,v,lval_op)])
      becauce i is less than the length of dxel, and dxel length equals to x
      which means we are only accessing the part that is inside x
      *)

     subgoal `
     i < LENGTH x ==>
     EL i x = EL i ( (x ⧺ [(varn_name x1,v,lval_op)]))` >-
     SIMP_TAC list_ss [Once EL_APPEND1,LENGTH_MAP] >>
     rw[] 
     ,
     IMP_RES_TAC distinct_not_neg_in_bound
     ]

   ]
   
   ,
   (* second side of the implication copyin_abstract ==> UPDATE *)

   fs[AUPDATE_def] >>
   Cases_on `ALOOKUP x (varn_name x1)` >>
   fs[] >| [

     IMP_RES_TAC copyin_abstract_distinct_app >>
     IMP_RES_TAC copyin_abstract_distinct >>
     IMP_RES_TAC args_ci_scope_LENGTH >>
     IMP_RES_TAC copyin_last_calculate >>
     fs[]
     ,
     IMP_RES_TAC copyin_abstract_distinct_app >>
     IMP_RES_TAC copyin_abstract_distinct >>
     IMP_RES_TAC distinct_not_neg_in_bound
     ]
 ]   
]
); 




val all_arg_update_eq = prove ( ``
! dxel ss scope.
     (ALL_DISTINCT (MAP (\(d,x,e).x) dxel)) ∧
     ( wf_arg_list
        (MAP (\(d,x,e).d) dxel)
	(MAP (\(d,x,e).x) dxel)
	(MAP (\(d,x,e).e) dxel) ss)  ==>
((all_arg_update_for_newscope (MAP (\(d,x,e).x) dxel) (MAP (\(d,x,e).d) dxel) (MAP (\(d,x,e).e) dxel) ss = SOME scope)
<=>
copyin_abstract (MAP (\(d,x,e).x) dxel) (MAP (\(d,x,e).d) dxel) (MAP (\(d,x,e).e) dxel) ss scope)
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC copyin_abstract_verbose >>
gvs[all_arg_update_for_newscope_def] >>
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:d`` , ``:'b`` |-> ``:string`` , ``:'c`` |-> ``:e``] zipped_list) >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`dxel`])) >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scope`])) >>
METIS_TAC []
);




val copyin_eq = prove ( ``
! e_x_d_list gscope scopest scope.
     (ALL_DISTINCT (MAP (λ(e,x,d). x) e_x_d_list)) ∧
     (wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
                  (MAP (λ(e,x,d). x) e_x_d_list)
		  (MAP (λ(e,x,d). e) e_x_d_list)
                  (scopest ⧺ gscope))  ==>
(
(SOME scope = copyin (MAP (λ(e,x,d). x) e_x_d_list)
        (MAP (λ(e,x,d). d) e_x_d_list)
	(MAP (λ(e,x,d). e) e_x_d_list) gscope scopest)
<=>
copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
                (MAP (λ(e,x,d). d) e_x_d_list)
		(MAP (λ(e,x,d). e) e_x_d_list) (scopest ⧺ gscope) scope)
``,

REPEAT STRIP_TAC >>
fs[copyin_def] >>
ASSUME_TAC all_arg_update_eq >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
`ZIP ((MAP (λ(e,x,d). d) e_x_d_list),
 ZIP ((MAP (λ(e,x,d). x) e_x_d_list) ,
      (MAP (λ(e,x,d). e) e_x_d_list)))`,
 `scopest ⧺ gscope`, `scope`
])) >>

rfs[] >>
rfs[map_distrub]
);







(**********************************************)
(* show implication copyin ==> well formed *)
(**********************************************)



val wf_arg_list_implied = prove (``

!dxel d (x:string) e ci_scope ss tmp.
 ALL_DISTINCT (MAP (λ(d,x,e). x) dxel ⧺ [x]) /\
 check_args_red (MAP (λ(d,x,e). d) dxel ⧺ [d])
          (MAP (λ(d,x,e). e) dxel ⧺ [e]) /\
 SOME ci_scope = update_arg_for_newscope ss (SOME tmp) (d,x,e) ==>
 wf_arg_list [d] [x] [e] ss
``,

REPEAT STRIP_TAC >>
fs[wf_arg_list_def] >>

REPEAT STRIP_TAC >>

`i = 0` by fs[] >>
rw[Once EL_compute] >>
fs[wf_arg_def] >>

fs[update_arg_for_newscope_def] >>
fs[one_arg_val_for_newscope_def] >>

Cases_on `is_d_out d` >>
fs[is_d_out_def] >| [
 (* is out *)
 Cases_on `get_lval_of_e e` >> fs[] >>
 Cases_on `lookup_lval ss x'` >> fs[]
 ,
 Cases_on `v_of_e e` >> fs[]
]
); 



val wf_arg_list_normalize_imp1 = prove ( ``
! dxel d x e ss .
(wf_arg_list (MAP (λ(d,x,e). d) dxel) (MAP (λ(d,x,e). x) dxel)
          (MAP (λ(d,x,e). e) dxel) ss /\
wf_arg_list [d] [x] [e] ss) ==>
(wf_arg_list (MAP (λ(d,x,e). d) dxel ⧺ [d])
              (MAP (λ(d,x,e). x) dxel ⧺ [x])
	      (MAP (λ(d,x,e). e) dxel ⧺ [e]) ss )
``,

SIMP_TAC list_ss [wf_arg_list_def] >>
REPEAT STRIP_TAC >>
Cases_on `dxel = []` >| [
 gvs[]
 ,
 INST_FST [`0`] >>
 INST_FST [`i`] >>

 Cases_on `LENGTH dxel = i` >| [
   gvs[] >>
   rfs[EL_LENGTH_simp] 
   ,
   gvs[] >>
   NTAC 3  (rfs[Once EL_APPEND1,LENGTH_MAP])
   ]
]
);



val check_args_red_normalize = prove (``
! dxel d e . 
check_args_red (MAP (λ(d,x,e). d) dxel ⧺ [d])
               (MAP (λ(d,x,e). e) dxel ⧺ [e]) <=>
(check_args_red (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel)	/\
 check_args_red [d] [e] ) ``,

Induct_on `dxel` >-
fs[check_args_red_def] >>
REPEAT STRIP_TAC >>
RES_TAC >>
PairCases_on `h` >>
fs[] >>
fs[check_args_red_def] >>
Cases_on `is_arg_red h0 h2` >> gvs[]
);




val update_new_scope_wf_args = prove ( ``
∀dxel ci_scope ss.
     ALL_DISTINCT (MAP (λ(d,x,e). x) dxel) /\
     check_args_red (MAP (λ(d,x,e). d) dxel)
          (MAP (λ(d,x,e). e) dxel) /\
     SOME ci_scope =
     FOLDL (update_arg_for_newscope ss) (SOME []) (dxel)
      ⇒
     wf_arg_list (MAP (λ(d,x,e). d) dxel)
                  (MAP (λ(d,x,e). x) dxel)
		  (MAP (λ(d,x,e). e) dxel) (ss) ``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC]  >>
fs[SNOC_APPEND] >-
fs[wf_arg_list_def] >>

PairCases_on `x` >>
fs[] >>

 `ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
 `check_args_red (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel)` by  IMP_RES_TAC check_args_red_normalize >>
 fs[] >>


 Cases_on `FOLDL (update_arg_for_newscope ss) (SOME []) dxel` >| [
  fs[update_arg_for_newscope_def]
  ,
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`x`, `ss`])) >>
  gvs[] >>
  IMP_RES_TAC wf_arg_list_implied >>
  IMP_RES_TAC wf_arg_list_normalize_imp1
 ]
);





val all_update_new_scope_wf_args = prove ( ``
∀e_x_d_list ci_scope ss.
     ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) /\
     check_args_red (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) /\
     SOME ci_scope =
     all_arg_update_for_newscope (MAP (λ(e_,x_,d_). x_) e_x_d_list)
       (MAP (λ(e_,x_,d_). d_) e_x_d_list) (MAP (λ(e_,x_,d_). e_) e_x_d_list)
       (ss) ⇒
     wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
       (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
       (ss) ``,

REPEAT STRIP_TAC >>
ASSUME_TAC update_new_scope_wf_args >>
fs[all_arg_update_for_newscope_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ZIP (MAP (λ(e_,x_,d_). d_) e_x_d_list,
    ZIP (MAP (λ(e_,x_,d_). x_) e_x_d_list,
         MAP (λ(e_,x_,d_). e_) e_x_d_list))`,
	 `ci_scope`, `ss`])) >>
rfs[] >>
rfs[map_distrub]		 
);





val copyin_imp_wf_args2 = prove ( ``
! e_x_d_list ci_scope gscope scopest .
ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) /\
check_args_red (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) /\
SOME ci_scope =
        copyin (MAP (λ(e_,x_,d_). x_) e_x_d_list)
          (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) gscope scopest ==>
( wf_arg_list
        (MAP (\(e,x,d).d) e_x_d_list)
	(MAP (\(e,x,d).x) e_x_d_list)
	(MAP (\(e,x,d).e) e_x_d_list) (scopest ++ gscope)) 
``,
fs[copyin_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC all_update_new_scope_wf_args
);






(****************************)
(* further lemmas about the copyin and the typing*)

val star_not_in_varn_list = prove ( ``
! scope xl .
MAP FST scope = mk_varn (xl) ==>
star_not_in_sl [scope] ``,

Induct_on `xl` >>
Induct_on `scope` >>
fs[mk_varn_def, star_not_in_sl_def, star_not_in_s_def] >>
REPEAT STRIP_TAC >>
PairCases_on `h` >> fs[]
);





val check_args_red_normalize2 = prove (``
! e_x_d_list d e . 
check_args_red (d::MAP (λ(e_,x_,d_). d_) e_x_d_list)
               (e::MAP (λ(e_,x_,d_). e_) e_x_d_list) ==>
(check_args_red (MAP (λ(e_,x_,d_). d_) e_x_d_list)
                (MAP (λ(e_,x_,d_). e_) e_x_d_list)/\
check_args_red [d] [e] ) ``,

Induct_on `e_x_d_list` >>
fs[check_args_red_def] >>
REPEAT STRIP_TAC >>
RES_TAC
);






(*********************************************)
(*** initilised values are also well typed ***)
(*********************************************)


val rm_t_def = Define `
(rm_t (t_tau (tau : tau) ) = tau ) 
`;


val type_of_v_def = TotalDefn.tDefine "type_of_v" `
(type_of_v (v_bool boolv) = t_tau tau_bool) /\
(type_of_v (v_bit (bl, n)) = t_tau (tau_bit n)) /\
(type_of_v (v_bot) = t_tau tau_bot) /\
(type_of_v (v_err x) = t_tau tau_err) /\
(type_of_v (v_str x) = t_string_names_a [x] ) /\
(type_of_v (v_struct xvl) =
  t_tau (tau_xtl struct_ty_struct ( MAP (\xv . (FST xv ,  rm_t (type_of_v (SND xv))   )) xvl   ) ) ) /\
(type_of_v (v_header boolv xvl) =
  t_tau (tau_xtl struct_ty_header ( MAP (\xv . (FST xv ,  rm_t (type_of_v (SND xv))   )) xvl   ) ) )
`
(WF_REL_TAC `measure v_size` >>
 fs[v_size_def] >>
 REPEAT STRIP_TAC >>
 `v_size p_2 < v1_size xvl` suffices_by (
  fs[]
 ) >>
 METIS_TAC [v1_size_mem]
);


val v_typ_eq_def = Define `
v_typ_eq v t (ty:'a itself)  = 
    (type_of_v v = t ==> v_typ v t F)
`;


val vl_typ_eq_def = Define `
vl_typ_eq vl tl (ty:'a itself)  = 
    ! i v t. (EL i vl = v) /\ (EL i tl = t) ==> v_typ_eq v t (ty:'a itself)
`;



(* this property is applied only on the base type. It does not include the parer names*)
val init_out_v_typed_def = Define `
 init_out_v_typed (v:v) (ty:'a itself) =
(!tau . v_typ v (t_tau tau) F ==> v_typ (init_out_v v) (t_tau tau) F)
`;


val init_out_svl_typed_def = Define `
 init_out_svl_typed (svl: (string # v) list ) (ty:'a itself) =
   !  (v:v) . MEM v (SND (UNZIP svl)) ==> init_out_v_typed (v) (ty:'a itself)
`;

val init_out_sv_tup_typed_def = Define `
 init_out_sv_tup_typed (tup : (string#v) ) (ty:'a itself) =
     init_out_v_typed ((SND tup)) (ty:'a itself)
`;


(* init all varn in a list *)
val init_out_v_list = Define `
init_out_v_list (vl:v list) =
MAP (\v. init_out_v v ) vl
`;



val init_struct = prove (``
! xl vl b.
LENGTH xl = LENGTH vl ==>
(init_out_v (v_struct (ZIP (xl, vl))) = v_struct (ZIP (xl, MAP init_out_v vl)) /\
 init_out_v (v_header b (ZIP (xl, vl))) = v_header F (ZIP (xl, MAP init_out_v vl))) ``,

Induct_on `xl` >>
Induct_on `vl` >>
fs[] >>
fs[init_out_v_def] >>
REPEAT STRIP_TAC >>
RES_TAC >>

fs[ZIP_MAP] >>
fs[ELIM_UNCURRY]
);



val init_typed =
prove (``
(! (ty:'a itself) .
(! v    . init_out_v_typed v (ty:'a itself) ) /\
(! (svl). init_out_svl_typed svl ty) /\
(! (sv) . init_out_sv_tup_typed sv ty)) ``,


STRIP_TAC >>
Induct >>
fs[init_out_v_typed_def] >> 
REPEAT STRIP_TAC >>
fs[Once v_typ_cases] >>
fs[init_out_v_typed_def, init_out_v_def] >| [

  (*v_bit*)
 REPEAT STRIP_TAC >>
 Cases_on `p` >>
 srw_tac [SatisfySimps.SATISFY_ss][init_out_v_def] >>
 fs[bs_width_def, extend_def]
 
 ,

 (*v_struct*)
 fs[clause_name_def] >>
 rw[] >>

 Q.EXISTS_TAC `
 ZIP ( (MAP (λ(x_,v_,tau_). x_) x_v_tau_list),
 ZIP ( (init_out_v_list ((MAP (λ(x_,v_,tau_). v_) x_v_tau_list) ) )   ,
       (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)))` >>
 fs[] >>

 fs[map_distrub, map_rw1] >>

 fs[lambda_unzip_tri] >>
 fs[lambda_12_unzip_tri] >>
 fs[map_tri_zip12] >>
 EVAL_TAC >>
 fs[GSYM UNZIP_MAP] >>
 fs[MAP_ZIP] >> CONJ_TAC  >|[

   ASSUME_TAC init_struct >>
   gvs[] 
   ,

   REPEAT STRIP_TAC >>

   fs[UNZIP_MAP] >>
   fs[init_out_svl_typed_def] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(EL i (MAP FST (MAP SND (x_v_tau_list: (string # v # tau) list)))) `])) >>


   subgoal `! (l: (string # v # tau) list ) .MAP FST (MAP SND l) =
                                             MAP (λ(x_,v_,tau_). v_) l ` >-
     (Induct_on `l` >>
      REPEAT STRIP_TAC >>
      fs[] >> PairCases_on `h` >>
      gvs[] ) >>


   subgoal `MEM (EL i (MAP FST (MAP SND x_v_tau_list)))
          (MAP (λ(x_,v_,tau_). v_) x_v_tau_list)` >-
     (fs[EL_MEM, MEM_EL] >>
     Q.EXISTS_TAC `i` >>
     fs[]) >>
	  
   gvs[] >>
   fs[init_out_v_typed_def] >>

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`EL i (MAP SND (MAP SND (x_v_tau_list:(string # v # tau) list ))) `])) >>
   gvs[] >>

   subgoal `! (l: (string # v # tau) list ) .MAP SND (MAP SND l) =
                                             MAP (λ(x_,v_,tau_). tau_) l ` >-
     (Induct_on `l` >>
      REPEAT STRIP_TAC >>
      fs[] >>
      PairCases_on `h` >>
      gvs[] ) >>



   subgoal `MEM (EL i (MAP SND (MAP SND x_v_tau_list)))
          (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)` >-
	  (fs[EL_MEM, MEM_EL] >>
          Q.EXISTS_TAC `i` >>
	  fs[]) >>

   gvs[] >>

   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v)``, ``:'b`` |-> ``:(v)``] P_on_any_EL) >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP (λ(x_,v_,tau_). v_) (x_v_tau_list : (string # v # tau) list))`
    , `i`, ` init_out_v `])) >>
   gvs[] 
  ]

,

 (*same as above*)
 (*v_struct*)
 fs[clause_name_def] >>
 rw[] >>

 Q.EXISTS_TAC `
 ZIP ( (MAP (λ(x_,v_,tau_). x_) x_v_tau_list),
 ZIP ( (init_out_v_list ((MAP (λ(x_,v_,tau_). v_) x_v_tau_list) ) )   ,
       (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)))` >>
 Q.EXISTS_TAC `F` >>      
 fs[] >>

 fs[map_distrub, map_rw1] >>

 fs[lambda_unzip_tri] >>
 fs[lambda_12_unzip_tri] >>
 fs[map_tri_zip12] >>
 EVAL_TAC >>
 fs[GSYM UNZIP_MAP] >>
 fs[MAP_ZIP] >> CONJ_TAC  >|[

   ASSUME_TAC init_struct >>
   gvs[] 
   ,

   REPEAT STRIP_TAC >>

   fs[UNZIP_MAP] >>
   fs[init_out_svl_typed_def] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(EL i (MAP FST (MAP SND (x_v_tau_list: (string # v # tau) list)))) `])) >| [

   fs[Once v_typ_cases]
   ,
   subgoal `! (l: (string # v # tau) list ) .MAP FST (MAP SND l) =
                                             MAP (λ(x_,v_,tau_). v_) l ` >-
     (Induct_on `l` >>
      REPEAT STRIP_TAC >>
      fs[] >> PairCases_on `h` >>
      gvs[] ) >>


   subgoal `MEM (EL i (MAP FST (MAP SND x_v_tau_list)))
          (MAP (λ(x_,v_,tau_). v_) x_v_tau_list)` >-
     (fs[EL_MEM, MEM_EL] >>
     Q.EXISTS_TAC `i` >>
     fs[]) >>
	  
   gvs[] >>
   fs[init_out_v_typed_def] >>

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`EL i (MAP SND (MAP SND (x_v_tau_list:(string # v # tau) list ))) `])) >>
   gvs[] >>

   subgoal `! (l: (string # v # tau) list ) .MAP SND (MAP SND l) =
                                             MAP (λ(x_,v_,tau_). tau_) l ` >-
     (Induct_on `l` >>
      REPEAT STRIP_TAC >>
      fs[] >>
      PairCases_on `h` >>
      gvs[] ) >>



   subgoal `MEM (EL i (MAP SND (MAP SND x_v_tau_list)))
          (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)` >-
	  (fs[EL_MEM, MEM_EL] >>
          Q.EXISTS_TAC `i` >>
	  fs[]) >>

   gvs[] >>

   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v)``, ``:'b`` |-> ``:(v)``] P_on_any_EL) >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP (λ(x_,v_,tau_). v_) (x_v_tau_list : (string # v # tau) list))`
    , `i`, ` init_out_v `])) >>
   gvs[]
   ]
 ]
 ,
 fs[Once v_typ_cases]
 ,
 fs[init_out_svl_typed_def]
 ,

 fs[init_out_svl_typed_def] >>
 fs[init_out_sv_tup_typed_def] >>

 REPEAT STRIP_TAC >>
 gvs[]

 ,


 fs[init_out_sv_tup_typed_def] >>
 fs[init_out_v_typed_def] >>
 RW_TAC (srw_ss()) [] >>

 Cases_on `v` >>
 fs[clause_name_def] THEN_LT (
 NTH_GOAL (  OPEN_V_TYP_TAC ``v_struct l`` >>
             INST_FST [`tau:tau`] >> 
             METIS_TAC[]) 4 )

 THEN_LT (
 NTH_GOAL (  OPEN_V_TYP_TAC ``v_struct l`` >>
             INST_FST [`tau:tau`] >> 
             METIS_TAC[]) 4 ) >>

 TRY (PairCases_on `p`) >>
 Cases_on `tau` >> fs[Once v_typ_cases] >>
 fs[Once v_typ_cases] 
]
);



val FIND_in_conc = prove( ``
! xtl s a . 
FIND (λx. FST x = s) xtl = SOME a ==>
     (FST a=s) ``,

Induct_on `xtl` >>
REPEAT STRIP_TAC >>
fs[FIND_def, INDEX_FIND_def] >>
Cases_on ` FST h = s` >> gvs[] >>
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#'b)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`, `xtl`, `(λx. FST x = s)`, `z`])) >>
   gvs[GSYM ADD1] >> 
RES_TAC
);




val access_struct_init_typed = prove ( ``
! x s v struct_ty x_tau_list tau .
v_typ x (t_tau (tau_xtl struct_ty x_tau_list)) F /\
acc_f x s = SOME v /\
correct_field_type x_tau_list s tau ==>
v_typ (init_out_v v) (t_tau tau) F

``,
REPEAT STRIP_TAC >>
fs[correct_field_type_def, tau_in_rec_def] >>

Cases_on `FIND (λ(xm,tm). xm = s) x_tau_list` >> fs[] >> rw[] >>
PairCases_on `x'` >> fs[] >>
Cases_on `x'1 = tau` >> fs[] >>
gvs[] >>
OPEN_V_TYP_TAC `x` >>
fs[] >>
gvs[] >>
fs[acc_f_def] >>

Cases_on `FIND (λ(f',v). f' = s) (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list)` >> fs[] >> rw[] >>
PairCases_on `x` >> fs[] >>
gvs[] >>
fs[FIND_def] >>
fs[] >>

REPEAT (

 PairCases_on `z` >>
 PairCases_on `z'` >>
 gvs[] >>

 subgoal `z0 = z'0` >-
  (IMP_RES_TAC INDEX_FIND_same_list >>
   gvs[]) >>
 rw[] >>

 `z'0 < LENGTH (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` by IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
 `EL z'0 (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) = (x0,v)` by IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
 `EL z'0 (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list) = (x'0,tau)` by IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
 gvs[] >>

 subgoal `v = EL z'0 (MAP (λ(x_,v_,tau_). v_) x_v_tau_list)` >-
  (IMP_RES_TAC EL_simp5 >>
   gvs[] ) >>

 subgoal `EL z'0 (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list) = tau ` >-
 (IMP_RES_TAC EL_ZIP_simp >>
  fs[] >>
  gvs[] ) >>

 subgoal `v_typ v (t_tau tau) F` >-
 (INST_FST [`z'0`] >>
  RES_TAC >>
  gvs[] ) >>


 ASSUME_TAC init_typed >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`ty`])) >>


 Q.PAT_X_ASSUM ` ∀v. init_out_v_typed v ty `
 (STRIP_ASSUME_TAC o (Q.SPECL [`v`])) >> 

 fs[init_out_v_typed_def]
));





val ev_not_typed_T = prove ( ``! t_g t_sl T_e v tau .
   ~ e_typ (t_g,t_sl) T_e (e_v v) (t_tau tau) T``,

fs[Once e_typ_cases] >>
fs[Once v_typ_cases] >>
gvs[]
);



val lookup_lval_exsists = prove ( ``
! ss v x s .
lookup_lval (ss) (lval_field x s) = SOME v ==>
? v' . lookup_lval (ss) x = SOME v' ``,

REPEAT STRIP_TAC >>
fs[lookup_lval_def] >>
Cases_on `lookup_lval ss x` >>
fs[] );



val acc_struct_val_typed = prove ( ``
! v strct s struct_ty x_tau_list tau .
acc_f strct s = SOME v /\
v_typ strct (t_tau (tau_xtl struct_ty x_tau_list)) F /\
correct_field_type x_tau_list s tau ==>
  v_typ v (t_tau tau) F
``,

REPEAT STRIP_TAC >>
fs[correct_field_type_def, tau_in_rec_def] >>

Cases_on `FIND (λ(xm,tm). xm = s) x_tau_list` >> fs[] >>
PairCases_on `x` >> fs[] >>
Cases_on `x1=tau` >> gvs[] >>

OPEN_V_TYP_TAC ``strct`` >>
fs[FIND_def] >>
Cases_on `z` >> gvs[] >>

`q < LENGTH (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` by IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
`EL q (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list) = (x0,tau)` by IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>

gvs[] >>
RES_TAC >>

fs[acc_f_def] >>
Cases_on `FIND (λ(f',v). f' = s) (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list)` >> fs[] >>
PairCases_on `x` >> fs[] >> gvs[] >>
fs[FIND_def] >>
Cases_on `z` >> gvs[] >>

IMP_RES_TAC INDEX_FIND_same_list >> 
gvs[] >>
RES_TAC >>

(subgoal ` v = EL q (MAP (λ(x_,v_,tau_). v_) x_v_tau_list)` >-
 (`EL q (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) = (x0',v)` by fsrw_tac [] [INDEX_FIND_EQ_SOME_0] >>
   IMP_RES_TAC EL_simp5 >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`v`, `x0'`])) >>
   gvs[]
 )) >>
gvs[]
);





val out_dir_lookup_typed = prove ( ``
! e tau lval T_e gscope t_g scopest t_sl b d (x:string).
type_scopes_list gscope t_g /\
type_scopes_list scopest t_sl /\
star_not_in_sl scopest /\
get_lval_of_e e = SOME lval /\
wf_arg d x e (scopest ⧺ gscope) /\
(is_d_out d ) /\
e_typ (t_g,t_sl) T_e e (t_tau tau) b ==>
(? v . lookup_lval (scopest ⧺ gscope) lval = SOME v /\
v_typ v (t_tau tau) F)
``,
(* First prove that b is always true *)


fs[wf_arg_def, is_d_out_def] >> 
Induct >>
REPEAT STRIP_TAC >>
fs[get_lval_of_e_def] >>
gvs[] >| [

 (* variables case *)
 Cases_on `v` >> 
 gvs[] >>
 fs[Once e_typ_cases] >>

 (*prep for the similarity lemma *)
 fs[lookup_lval_def, lookup_v_def, lookup_tau_def] >| [

  Cases_on `lookup_map (scopest ⧺ gscope) (varn_name s)` >>
  Cases_on `lookup_map (t_sl ⧺ t_g) (varn_name s)` >>
  gvs[] >>

  fs[type_scopes_list_def] >>
  subgoal `similarl (λx y. v_typ (FST x) (t_tau y) F) (scopest ++ gscope) (t_sl ++ t_g) ` >-
  (fs[similarl_def] >>
  IMP_RES_TAC LIST_REL_APPEND) >>

  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                         ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>
			 
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`(λx y. v_typ (FST x) (t_tau y) F)`,
   `(tau)`,
   `(varn_name s)`,
   `x`,
   `(t_sl ⧺ t_g)`,
   `(scopest ⧺ gscope)`])) >>
   PairCases_on `x` >>
   gvs[]
   ,

   fs[find_star_in_globals_def] >>

   Cases_on `lookup_map (scopest ⧺ gscope) (varn_star f)` >>
   Cases_on `lookup_map t_g (varn_star f)` >>
   gvs[] >>
   PairCases_on `x` >>
   gvs[] >>

   subgoal `lookup_map (gscope) (varn_star f) = SOME (v',x1)` >-
   ( ASSUME_TAC lookup_map_in_gsl_lemma >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`v'`,`x1`, `f`, `scopest`, `gscope`])) >>
    RES_TAC >> gvs[] ) >>
  
   fs[type_scopes_list_def] >>
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                         ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(λx y. v_typ (FST x) (t_tau y) F)`,
    `(tau)`,
    `(varn_star f)`,
    `(v',x1)`,
    `(t_g)`,
    `(gscope)`])) >>
   gvs[] 
   ]
 , 

 (* acc *)

 Cases_on `get_lval_of_e e` >> fs[] >>
 OPEN_EXP_TYP_TAC ``(e_acc e s)`` >> fs[] >>

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(tau_xtl struct_ty x_tau_list)`,
  `T_e`,
  `gscope`,
  `t_g`,
  `scopest`,
  `t_sl` , `b`, `d`])) >>
 gvs[] >>

 IMP_RES_TAC lookup_lval_exsists  >>
 gvs[] >>

 (*
 now show that the value v is well tped, and this is true, because v is being taken from
 the struct v', and the truct v' is well typed, and also the tau that typed v is in that struct.
 *)

 fs[lookup_lval_def] >>
 Cases_on `d` >> 
 IMP_RES_TAC acc_struct_val_typed >>
 fs[is_d_out_def]
 ,

 (* slice *)

 Cases_on `get_lval_of_e e` >> fs[] >>
 OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >> fs[] >>

 fs[get_lval_of_e_def] >>
 gvs[] >>

 fs[lookup_lval_def] >>
 Cases_on `lookup_lval (scopest ⧺ gscope) x` >> fs[] >>
 Cases_on `x'` >> fs[] >>
 PairCases_on `p` >> fs[] >>

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(tau_bit w)`,
  `T_e`,
  `gscope`,
  `t_g`,
  `scopest`,
  `t_sl` , `b`, `d`])) >>
 gvs[] >>

 fs[slice_lval_def] >>
 PairCases_on `bitv` >> PairCases_on `bitv'` >>
 gvs[] >>

 fs[Once v_typ_cases] >>
 gvs[slice_def, bs_width_def, bitv_bitslice_def, vec_to_const_def]
]
);





val CI_scope_WT_single = prove ( ``
! e gscope t_g scopest t_sl x d tau T_e scope' b t.
type_scopes_list gscope t_g /\
type_scopes_list scopest t_sl /\
star_not_in_sl scopest /\
( e_typ (t_g,t_sl) T_e e (t_tau tau) b) /\
wf_arg d x e (scopest ⧺ gscope) /\
copyin_abstract [x] [d] [e] (scopest ⧺ gscope) scope' ==>
type_scopes_list [scope'] [ZIP ((mk_varn [x]), [tau])]
``,


fs[type_scopes_list_def] >>
fs[mk_varn_def] >>
REPEAT STRIP_TAC >>
Cases_on `is_d_out d` >>

SIMP_TAC list_ss [similarl_def, similar_def] >>
fs[mk_varn_def] >>
fs[copyin_abstract_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`0`])) >>
fs[] >>


Cases_on `one_arg_val_for_newscope d e (scopest ⧺ gscope)` >>
fs[] >>
PairCases_on `x'` >>
Q.EXISTS_TAC `(varn_name x,x'0,x'1)` >>
gvs[] >| [

(** inout & out directed **)

  subgoal `scope' = [(varn_name x,x'0,x'1)]` >-
  (Induct_on `scope'` >>
  fs[]) >>
  fs[] >> rw[] >>

  fs[wf_arg_def, is_d_out_def] >>

  fs[one_arg_val_for_newscope_def, is_d_out_def] >> gvs[] >>

  Cases_on `is_d_in d` >> fs[] >> gvs[] >>

    (* inout *)
    ASSUME_TAC out_dir_lookup_typed >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
    [`e`,`tau`,  `lval`, `T_e`, `gscope`, `t_g`,
    `scopest`, `t_sl`, `b`, `d`, `x`])) >>
    gvs[type_scopes_list_def] >>
    fs[wf_arg_def] >>
    (* out *)
    ASSUME_TAC init_typed >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
    [`ty`])) >>
    fs[] >>
    fs[init_out_v_typed_def]

  ,

  subgoal `scope' = [(varn_name x,x'0,x'1)]` >-
  (Induct_on `scope'` >>
  fs[]) >>
  fs[] >> rw[] >>

  fs[one_arg_val_for_newscope_def] >>

  Cases_on `is_d_out d` >> fs[] >>

  Cases_on `v_of_e e` >> fs[] >> rw[] >>
  Cases_on `e` >> fs[is_const_def, v_of_e_def] >>
  rw[] >>

  Cases_on `b` >>
  IMP_RES_TAC ev_not_typed_T >>
  IMP_RES_TAC ev_types_v
]);


val similar_normalize = prove ( ``
∀l vl tl t v R a.
       LENGTH vl = LENGTH tl ∧ similar R [a] (ZIP ([v],[t])) ∧
       similar R l (ZIP (vl,tl)) ⇒
       similar R (a::l) (ZIP (v::vl,t::tl))``,

REPEAT STRIP_TAC >>
fs[similar_def]
);



val CI_scope_list_typed = prove (``
! e_x_d_list scopest t_sl gscope t_g scope' e_tau_d_b_list T_e.
(LENGTH e_tau_d_b_list = LENGTH e_x_d_list) /\
type_scopes_list gscope t_g /\
type_scopes_list scopest t_sl /\
star_not_in_sl scopest /\
(∀i. i < LENGTH e_tau_d_b_list ⇒
            e_typ (t_g,t_sl)
              (T_e)
              (EL i (MAP (λ(e_,x_,d_). e_) e_x_d_list))
              (t_tau (EL i (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)))
              (EL i (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list))) /\
wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list) 
            (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
            (scopest ⧺ gscope) /\
copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
          (MAP (λ(e,x,d). d) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope) scope' ==>
type_scopes_list [scope']
          [ZIP (mk_varn (MAP (λ(e_,x_,d_). x_) e_x_d_list),
              MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)] ``,	  
Induct >| [

 REPEAT STRIP_TAC >> fs[] >>
 fs[similar_def, copyin_abstract_def] >>
 SIMP_TAC list_ss [type_scopes_list_def, mk_varn_def] >>
 fs[similarl_def, similar_def] 
 ,

 REPEAT STRIP_TAC >> fs[] >>
 PairCases_on `h` >> fs[] >>

 (* first show that the head is well typed*)
 subgoal `type_scopes_list [[HD scope']]
          [ZIP (mk_varn [h1],[HD (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)])] `  >- (	  
   `wf_arg h2 h1 h0 (scopest ⧺ gscope)` by IMP_RES_TAC wf_arg_normalization >>
     subgoal `copyin_abstract [h1] [h2] [h0] (scopest ⧺ gscope) [HD scope']` >-
       (IMP_RES_TAC copyin_abstract_normalize_tmp >>
        rfs[] ) >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>

  gvs[] >>
  ASSUME_TAC CI_scope_WT_single >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`h0`, `gscope`, `t_g`, `scopest`, `t_sl`, `h1`, `h2`,
  `(HD (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (α # tau # β # bool) list)))`,
  `T_e`, `[HD scope']`,
  `(HD (MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list : (α # tau # β # bool) list)))`])) >>
  gvs[] ) >>


 (* now use the IH to show that the TL of the CI scope is also well type *)

 `wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
          (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope)` by IMP_RES_TAC wf_arg_normalization >>
	  
 `copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
          (MAP (λ(e,x,d). d) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope) (TL scope')` by (IMP_RES_TAC copyin_abstract_normalize_tmp >>
                                              rfs[] ) >>
					      
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`scopest`,`t_sl`, `gscope`,`t_g`, `TL scope'`, `TL e_tau_d_b_list`, `T_e` ])) >>

   subgoal `LENGTH (TL e_tau_d_b_list) = LENGTH e_x_d_list` >-
     (Cases_on `e_tau_d_b_list` >>
      Cases_on `e_x_d_list` >>
      fs[] ) >>
   gvs[] >>


  subgoal `(∀i. i < LENGTH e_x_d_list ⇒
             e_typ (t_g,t_sl) T_e
	                  (EL i (MAP (λ(e_,x_,d_). e_) e_x_d_list))
               (t_tau (EL i (MAP (λ(e_,tau_,d_,b_). tau_) (TL e_tau_d_b_list))))
                          (EL i (MAP (λ(e_,tau_,d_,b_). b_) (TL e_tau_d_b_list))))` >-
    ( REPEAT STRIP_TAC >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i + 1` ])) >>
      gvs[ADD1] >>
      fs[EL_CONS] >>
      fs[PRE_SUB1] >>

      fs[Once EL_compute] >>
      Cases_on `i=0` >> gvs[] >| [
        Induct_on `e_tau_d_b_list` >> fs[]
        ,
        gvs[numeral_pre, PRE_SUB1,PRE_SUC_EQ] >>
        `LENGTH e_tau_d_b_list > 0 ` by fs[] >>

      subgoal `(EL (i + 1) (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)) =
               (EL i   (MAP (λ(e_,tau_,d_,b_). tau_) (TL e_tau_d_b_list))) ` >-
        ( `EL (SUC i) (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list) =
           EL i (TL (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list)))` by gvs[EL] >>
           fs[ADD1] >>
           fs[EL, MAP_TL] ) >>

      subgoal `(EL (i + 1) (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list)) =
               (EL   i (MAP (λ(e_,tau_,d_,b_). b_) (TL e_tau_d_b_list))) ` >-
        ( `EL (SUC i) (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list) =
           EL   i (TL (MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list)))` by gvs[EL] >>
           fs[ADD1] >>
           fs[EL, MAP_TL] ) >>
           fs[]
      ]) >>	       


 gvs[] >>
 fs[type_scopes_list_def] >>
 fs[similarl_def] >>


 (* make a similar relation *)
 ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(varn)`` ,
                        ``:'b`` |-> ``:(v # lval option)`` ,
   		                  ``:γ`` |-> ``:(tau)``] similar_normalize)  >>


 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`TL (scope')`,
  ` (mk_varn (MAP (λ(e_,x_,d_). x_) (e_x_d_list : (e # string # d) list)))`,
  `MAP (λ(e_,tau_,d_,b_). tau_) (TL (e_tau_d_b_list : (α # tau # β # bool) list))`,
  `HD (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (α # tau # β # bool) list))`,
  `varn_name h1`,
  `(λx y. v_typ (FST x) (t_tau y) F)`,
  `HD scope'`
 ])) >>


 gvs[] >>
 fs[mk_varn_def] >>
 gvs[] >>


 subgoal `(HD scope'::TL scope' ) = scope'` >-
 (IMP_RES_TAC args_ci_scope_LENGTH2 >> gvs[] >>
  `LENGTH scope' > 0` by fs[] >>
  fs[quantHeuristicsTheory.HD_TL_EQ_THMS] >>
  fs[NOT_NIL_EQ_LENGTH_NOT_0]) >>


 gvs[] >>
 fs[EL, MAP_TL] >> 

 fs[similar_def] >> gvs[] >>
 PairCases_on `x` >>
 gvs[] >>


 Q.EXISTS_TAC `(varn_name h1,  (HD (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list))  )` >>
 Q.EXISTS_TAC `(ZIP (MAP (λx. varn_name x) (MAP (λ(e_,x_,d_). x_) e_x_d_list),
                 TL (MAP (λ(e_,tau_,d_,b_). tau_) ( e_tau_d_b_list))))` >>
	  gvs[] >>
	  rw[] >>
	  rfs[] >>    

 fs[ZIP_def, ZIP] >>
 (*should be simple now to prove*)


   subgoal `(HD (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)::
             TL (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list) ) =
             (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list)` >-
  (`LENGTH e_tau_d_b_list > 0` by fs[] >> 
   fs[quantHeuristicsTheory.HD_TL_EQ_THMS] >>
   fs[NOT_NIL_EQ_LENGTH_NOT_0]) >>

  `∀x1 (l1: varn list) x2 (l2:tau list).
    ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)` by fs[ZIP_def] >>

 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`varn_name h1 `,
   `MAP (λx. varn_name x) (MAP (λ(e_,x_,d_). x_) (e_x_d_list : (e # string # d) list))`,
   `HD (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (α # tau # β # bool) list))`,
   `TL (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (α # tau # β # bool) list))`])) >>
   METIS_TAC[]
]
 );















(****************)
(****************)
(*  E SR        *)
(****************)
(****************)

val SR_e =
prove (`` ! (ty:'a itself) .
(!e. sr_exp e ty) /\
(! (l1: e list). sr_exp_list l1 ty) /\
(! (l2: (string#e) list) .  sr_strexp_list l2 ty) /\
(! tup. sr_strexp_tup tup ty)   ``,

STRIP_TAC >>
Induct >| [ 

(*****************)
(*    values     *)
(*****************)

FULL_SIMP_TAC list_ss [sr_exp_def, lemma_v_red_forall]
,

(*****************)
(*   variables   *)
(*****************)

rfs[sr_exp_def] >>
REPEAT STRIP_TAC >>


OPEN_EXP_RED_TAC ``(e_var v)`` >>
OPEN_EXP_TYP_TAC ``(e_var v)`` >>

FULL_SIMP_TAC list_ss [] >> 
fs[clause_name_def] >>
rw[] >|[

 (*variable name not a star*)
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 fs[clause_name_def] >>
 Q.EXISTS_TAC `F` >>
 IMP_RES_TAC varn_is_typed
 ,

 (* thm requires the typing context *)
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 fs[clause_name_def] >>
 Q.EXISTS_TAC `F` >>

 subgoal `! t_scope_list_g x.
          find_star_in_globals t_scope_list_g x = lookup_tau [] t_scope_list_g x ` >-
  fs[find_star_in_globals_def, lookup_tau_def] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`t_scope_list_g`, `(varn_star funn')`])) >>

 IMP_RES_TAC lookup_in_gsl_lemma >>

 subgoal `type_scopes_list [] []` >-
 fs[type_scopes_list_def, similarl_def] >>

 gvs[] >>
 IMP_RES_TAC varn_is_typed
]

,

(*****************)
(*expression list*)
(*****************)

fs[sr_exp_list_def] >>
rfs[sr_exp_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once e_red_cases]

,

(*****************)
(* field access  *)
(*****************)

SIMP_TAC list_ss [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_acc e s)`` >>
FULL_SIMP_TAC list_ss [lemma_v_red_forall] >> rw[] >|[

 (*access a struct value*)
 
 OPEN_EXP_TYP_TAC ``(e_acc (e_v (v_struct f_v_list)) s)`` >>
 rw[] >>
 OPEN_EXP_TYP_TAC ``(e_v (v_struct f_v_list))`` >>
 rw[] >>
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 rw[] >>
 OPEN_V_TYP_TAC ``(v_struct f_v_list)`` >>
 rw[] >>
 fs[clause_name_def]  >>
 rw[] >>

 rfs[FIND_def, MEM_EXISTS] >>
 Cases_on `z` >>
 Cases_on `r` >>
 gvs[] >>
 IMP_RES_TAC prop_in_range >>
 fs[LENGTH_MAP] >>
 
 subgoal `v_typ (EL q (MAP (λ(x_,v_,tau_). v_) x_v_tau_list))
          (t_tau (EL q (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list))) F ` >- (
  RES_TAC ) >>
 rw[] >>

 IMP_RES_TAC EL_relation_to_INDEX_less >>
 fs[LENGTH_MAP] >>
 subgoal `EL q (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) = (q',r')` >-
 RES_TAC >>
 rw[] >>
 
 IMP_RES_TAC EL_simp5 >>
 (*dont rewrite here*)
 IMP_RES_TAC correct_field_index_lemma >>
 Q.EXISTS_TAC `F` >>
 rfs[] 
 ,

 (*e_acc_arg1*)

 fs[sr_exp_def] >>
 OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
 rw[] >>
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 rw[] >>
 RES_TAC >>
 METIS_TAC[] (*instead of the quantifiers*)
 ,

 (*e_h_acc*)
 (*same as the first one  SIMPLIFY later*)
 OPEN_EXP_TYP_TAC ``(e_acc (e_v (v_header boolv f_v_list)) s)`` >>
 rw[] >>
 OPEN_EXP_TYP_TAC ``(e_v (v_header boolv f_v_list))`` >>
 rw[] >>
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 rw[] >>
 OPEN_V_TYP_TAC ``(v_struct f_v_list)`` >>
 rw[] >>
 fs[clause_name_def]  >>
 rw[] >>

 rfs[FIND_def, MEM_EXISTS] >>
 Cases_on `z` >>
 Cases_on `r` >>
 IMP_RES_TAC prop_in_range >>
 fs[LENGTH_MAP] >>

 subgoal `v_typ (EL q (MAP (λ(x_,v_,tau_). v_) x_v_tau_list))
          (t_tau (EL q (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list))) F ` >- (
  RES_TAC ) >>
 rw[] >>

 IMP_RES_TAC EL_relation_to_INDEX_less >>
 fs[LENGTH_MAP] >>
 subgoal `EL q (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) = (q',r')` >-
 RES_TAC >>
 rw[] >>
 IMP_RES_TAC EL_simp5 >>
 (*dont rewrite here*)
 IMP_RES_TAC correct_field_index_lemma >>
 Q.EXISTS_TAC `F` >>
 rfs[]
 ,

 (*frame creation must be also well-typed*)
 OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
 fs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
 ]
,

(*****************)
(*  unary oper   *)
(*****************)

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [sr_exp_def] >>
REPEAT STRIP_TAC >| [
 Cases_on `u` >>
 fs[sr_exp_def] >| [

   (*unop_neg*)
   OPEN_EXP_RED_TAC ``(e_unop u e)`` >>
   OPEN_EXP_TYP_TAC ``e_unop unop_neg e`` >>
   FULL_SIMP_TAC list_ss [lemma_v_red_forall] >>
   rw[] >-
     ( (*e*) EXP_GOAL_TYP_IH_TAC)  >>

     (*v*)
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
     SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
     fs[clause_name_def]
 
   ,

   (*unop_compl*)
   OPEN_EXP_TYP_TAC ``e_unop unop_compl e`` >>
   OPEN_EXP_RED_TAC ``e_unop unop_compl e`` >>
   FULL_SIMP_TAC list_ss [] >>
   rw[] >-
     ( (*e*) EXP_GOAL_TYP_IH_TAC)  >>
     
     OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>
     fs[] >>
     rw[] >>
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
     SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
     OPEN_V_TYP_TAC ``(v_bit bitv)`` >>

     fs[clause_name_def] >>
     rw[clause_name_def, bs_width_def] >>
     PairCases_on `bitv` >>
     FULL_SIMP_TAC std_ss [bs_width_def, bitv_bl_unop_def]

    ,

     (*e_unop unop_neg_signed e*)

     OPEN_EXP_TYP_TAC ``e_unop unop_neg_signed e`` >>
     OPEN_EXP_RED_TAC ``e_unop unop_neg_signed e`` >>
     FULL_SIMP_TAC list_ss [] >>
     rw[] >-
       ( (*e*) EXP_GOAL_TYP_IH_TAC)  >>


     OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>
     fs[] >>
     rw[] >>
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
     SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
     OPEN_V_TYP_TAC ``(v_bit bitv)`` >>

     rw[clause_name_def, bs_width_def] >>
     PairCases_on `bitv` >>
     FULL_SIMP_TAC std_ss [bs_width_def, bitv_bl_unop_def] >>
     fs[bs_width_neg_signed]

   ,

   (*unop_un_plus*)
   OPEN_EXP_TYP_TAC ``(e_unop unop_un_plus e)`` >>
   OPEN_EXP_RED_TAC ``(e_unop unop_un_plus e)`` >>
   FULL_SIMP_TAC list_ss [] >>
      rw[] >-
     ( (*e*) EXP_GOAL_TYP_IH_TAC)  >>
     
     OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >> rfs[] >>
     OPEN_V_TYP_TAC ``(v_bit bitv)`` >>
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
     SIMP_TAC (srw_ss()) [Once v_typ_cases] >> fs[]
  
]
,

(*resulted frame*)
 fs[] >>
 OPEN_EXP_RED_TAC ``(e_unop u e)`` >>
 OPEN_EXP_TYP_TAC ``(e_unop u e)`` >>
 rfs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
]


,

(****************)
(*  binop       *)
(****************)  



REPEAT STRIP_TAC  >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
REPEAT STRIP_TAC >| [

 Cases_on `is_const e` >| [
 Cases_on `is_const e'` >| [


    (* v op v *)
 Cases_on `e` >>
 Cases_on `e'` >>
 gvs[is_const_def] >>

   OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
   gvs[] >>

    OPEN_EXP_RED_TAC ``(e_binop e _ e')`` >>
    fs[] >>
    FULL_SIMP_TAC list_ss [lemma_v_red_forall] >>
    gvs[clause_name_def, is_bv_op_def, is_bool_op_def, is_err_bool_def, is_bv_bool_op_def] >>
    
     OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >>
     OPEN_EXP_TYP_TAC `` (e_v (v_bit bitv))`` >>
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>     
     SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
     gvs[] >>

     fs[Once v_typ_cases, clause_name_def] >>
     gvs[] >>
     
     PairCases_on `bitv` >>
     PairCases_on `bitv'` >>
     TRY(PairCases_on `bitv''`) >>
     rw[] >>
     rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
     rfs[bitv_binop_def] >>
     IMP_RES_TAC bitv_binop_inner_lemma 
    
     ,


(* case v op e *)

 Cases_on `e` >>
 gvs[is_const_def] >>

   OPEN_EXP_TYP_TAC ``(e_binop _ _ e')`` >>
   Cases_on `is_bv_op b` >| [


    OPEN_EXP_RED_TAC ``(e_binop _ _ e')`` >>
    fs[] >>
    FULL_SIMP_TAC list_ss [lemma_v_red_forall] >>
    gvs[clause_name_def, is_bv_op_def, is_bool_op_def, is_err_bool_def, is_bv_bool_op_def,
        is_short_circuitable_def, is_const_def] >>
    
     SIMP_TAC (srw_ss()) [Once e_typ_cases] >>

     gvs[clause_name_def, is_bv_op_def,
         is_bool_op_def, is_err_bool_def, is_bv_bool_op_def,
        is_short_circuitable_def, is_const_def] >>
      fs[sr_exp_def] >>
     METIS_TAC [sr_exp_def]  
     ,

    OPEN_EXP_RED_TAC ``(e_binop _ _ e')`` >>
    fs[] >>
    FULL_SIMP_TAC list_ss [lemma_v_red_forall] >>
    gvs[clause_name_def, is_bv_op_def, is_bool_op_def, is_err_bool_def, is_bv_bool_op_def,
        is_short_circuitable_def, is_const_def] >>
     srw_tac [SatisfySimps.SATISFY_ss][] >>
	
    
     ( SIMP_TAC (srw_ss()) [Once e_typ_cases] >>

     gvs[clause_name_def, is_bv_op_def,
         is_bool_op_def, is_err_bool_def, is_bv_bool_op_def,
        is_short_circuitable_def, is_const_def] >>
        srw_tac [boolSimps.DNF_ss][] >>
           METIS_TAC [sr_exp_def] )
     ]
  ]
,

  (* case e + e'*)
   OPEN_EXP_TYP_TAC ``(e_binop _ _ e')`` >>
   OPEN_EXP_RED_TAC ``(e_binop _ _ e')`` >>
   gvs[is_const_def] >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
     srw_tac [SatisfySimps.SATISFY_ss][] >>
    METIS_TAC [sr_exp_def]
]

,


 (***** frame creation ***)

 
 fs[] >>
 OPEN_EXP_RED_TAC ``(e_binop e b e')`` >>
 OPEN_EXP_TYP_TAC ``(e_binop e b e')`` >>
 rfs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
]

,

(****************)
(*  concat      *)
(****************)

SIMP_TAC std_ss [sr_exp_def] >>
REPEAT STRIP_TAC >| [

OPEN_EXP_RED_TAC ``(e_concat e e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >> gvs[] >>

OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
gvs[] >| [

 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 fs[sr_exp_def] >> METIS_TAC []
 ,
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 fs[sr_exp_def] >> METIS_TAC []
 ,
 rw[] >>
 SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
 OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>
  OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >>

 rw[] >>
 OPEN_V_TYP_TAC ``((v_bit bitv))`` >>
 OPEN_V_TYP_TAC ``((v_bit bitv'))`` >>
 fs[bitv_concat_def] >>
 SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
 Cases_on `bitv` >>
 Cases_on `bitv'` >>
 fs[bitv_concat_def] >>
 SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
 fs[bs_width_def]
 ]
,

fs[] >>
OPEN_EXP_RED_TAC ``(e_concat e e')`` >>
OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
rfs[] >>
srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
]

,

(****************)
(*   slice      *)
(****************)

SIMP_TAC std_ss [sr_exp_def] >>
REPEAT STRIP_TAC >|[

OPEN_EXP_RED_TAC ``(e_slice e e' e'')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >| [

gvs[] >>
OPEN_EXP_TYP_TAC ``(e_slice e (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>

rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
gvs[] >>
 fs[sr_exp_def] >>
 METIS_TAC []
 ,



gvs[] >>
OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >>

rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>


 SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
 FULL_SIMP_TAC (srw_ss()) [Once e_typ_cases] >>

 rfs[] >>
 OPEN_V_TYP_TAC ``(v_bit bitv)`` >>
 rfs[] >>
 
 PairCases_on `bitv` >>
 PairCases_on `bitv'` >>
 PairCases_on `bitv''` >>
 gvs[slice_def, bs_width_def, bitv_bitslice_def, vec_to_const_def]
 ]
,

 OPEN_EXP_RED_TAC ``(e_slice e e' e'')`` >>
 rw[] >>
 OPEN_EXP_TYP_TAC ``(e_slice e (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
]

,

(****************)
(*  call        *)
(****************)

fs[sr_exp_def] >>
REPEAT STRIP_TAC >| [

 (* the expression typing part *)
 
 OPEN_EXP_RED_TAC ``(e_call f l)`` >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 fs[] >| [
 
   (* reduction (call f -> star) where all args are reduced *)
   
   rw[] >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   fs[clause_name_def] >>
   rw[] >>


   OPEN_EXP_TYP_TAC ``(e_call f (MAP (λ(e_,x_,d_). e_) e_x_d_list))`` >>
   rw[] >>


   Q.EXISTS_TAC `(MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list)` >>
   fs[] >> rw[] >>

   
    IMP_RES_TAC Fg_star_lemma2 >> gvs[]
    
   ,
   
   (* reduction (call f el -> cal f el' ) where all args are reduced *)

   rw[] >>
   fs[clause_name_def] >>
   rw[] >>


   (*what we need to prove is *)
   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   fs[clause_name_def] >> rw[] >>


   subgoal `i < LENGTH e_e'_x_d_list` >- (
    IMP_RES_TAC unred_arg_index_in_range >>
    METIS_TAC[LENGTH_MAP] ) >>


   (*from the typing rule of calls, we know that *)
   OPEN_EXP_TYP_TAC `` (e_call f (MAP (λ(e_,e'_,x_,d_). e_) e_e'_x_d_list))`` >>
   fs[] >>
   gvs[] >>


   subgoal `i < LENGTH e_tau_d_b_list` >- (
    IMP_RES_TAC unred_arg_index_in_range >>
    METIS_TAC[LENGTH_MAP] ) >>
   RES_TAC >>


   (*for the ith argument, it indeed preserves the type *)
   subgoal `sr_exp (EL i (MAP (λ(e_,e'_,x_,d_). e_) e_e'_x_d_list)) ty`  >- (
    fs[sr_exp_list_def] >>
    IMP_RES_TAC unred_arg_index_in_range >>
    IMP_RES_TAC EL_MEM >>
    RES_TAC ) >>


   Q.PAT_X_ASSUM `sr_exp (EL i (MAP (λ(e_,tau_,d_,b_). e_) e_e'_x_d_list)) ty`
    ((STRIP_ASSUME_TAC o (Q.SPECL
    [`e''`,
     `gscope`,
     `scopest`,
     `framel`,
     `t_scope_list`,
     `t_scope_list_g`,
     `t_tau (EL i (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (e # tau # d # bool) list ) ))`,
     `(EL i (MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list : (e # tau # d # bool) list ) ))`,
     `(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)`, 
     `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
     `f'`, `f_called` , `stmt_called`,  `copied_in_scope`, `Prs_n` ])) o
    SIMP_RULE (srw_ss()) [sr_exp_def]) >>
   gvs[] >>


   Q.EXISTS_TAC `
   ZIP ( MAP (λ(e_,e'_,x_,d_). e'_) e_e'_x_d_list ,
        ZIP ( (MAP (λ(e_,tau_,d_,b_). tau_) e_tau_d_b_list),
        ZIP ( (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list) ,
     (LUPDATE b' i (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list))))) ` >>


   rw[map_rw_quad] >>
   IMP_RES_TAC lemma_MAP8 >>
   fs[] >| [

     FULL_SIMP_TAC std_ss  [map_rw2] 
     ,

     FULL_SIMP_TAC std_ss  [map_rw2]  >>
     Cases_on `i=i'` >>

     fs[] >>
     fs[EL_LUPDATE] >>
     RES_TAC >>
     rw[]
     ,


     (* the direction lists are the same *)
     subgoal ` (MAP (λ(e_,e'_,x_,d_). d_) e_e'_x_d_list) =
              (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)`>- 
      (ASSUME_TAC dir_fun_delta_same >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(MAP (λ(e_,e'_,x_,d_). (x_,d_)) (e_e'_x_d_list : (e # e # string # d) list)) `,
	 `(MAP (λ(e_,tau_,d_,b_). (tau_,d_)) (e_tau_d_b_list : (e # tau # d # bool) list))`,
	 `tau'`, `f`, `func_map`, `b_func_map`, `ext_map`,
	 `delta_g`, `delta_b`, `delta_x`, `apply_table_f`,
	 `order`, `t_scope_list_g`, `pars_map`, `tbl_map`])) >>
       gvs[] >>
       IMP_RES_TAC map_simp_1
	  ) >>


     (* if the arg is unred, then either out and not lval, or in and not const *)
     gvs[] >>
     IMP_RES_TAC unred_arg_index_result >| [
       (* in and not const *)
       IMP_RES_TAC dir_list_lemma1 >>
       gvs[ELIM_UNCURRY]
       ,
       (* out and lval *)
       subgoal  `(EL i (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list)) ==>
       is_e_lval (EL i (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list)) ` >-
       ( RES_TAC >>
         IMP_RES_TAC e_lval_tlval ) >>

       subgoal` is_d_out (EL i (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)) ⇒
                          EL i (MAP (λ(e_,tau_,d_,b_). b_) e_tau_d_b_list)` >-
       ( fs[out_is_lval_def] >>
         RES_TAC ) >>
       gvs[]
     ]
   ]
 ]
 ,


 (** frame creation part, theorem should show that the function being called
 and return a frame, everything in the frame should be well tyed, i.e. the statement and the scope*)

 OPEN_EXP_RED_TAC ``(e_call f l1)`` >>
 OPEN_EXP_TYP_TAC ``(e_call f l1)`` >>
 rfs[] >> rw[] >| [
 
   (*first subgoal of frame creation part *)
   
   fs[clause_name_def] >> rw[] >>
     
   drule tfunn_imp_sig_body_lookup >>
   REPEAT STRIP_TAC >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`MAP (λ(e_,tau_,d_,b_). (tau_,d_)) (e_tau_d_b_list : (e # tau # d # bool) list)`,
        `tau' `, `f`])) >>
   gvs[] >>


   (* we know that stmt_called and stmt are the same, and also same
	  for xdl and the map to x d *)

   Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >>
   gvs[] >>
       
   Q.EXISTS_TAC `[ZIP (mk_varn (MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list)),
                                MAP FST (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list))]` >>
   gvs[] >>

   SIMP_TAC list_ss [frame_typ_cases] >>
   fs[type_frame_tsl_def] >>
   fs[stmtl_typ_cases] >>
   fs[type_ith_stmt_def] >>
   fs[clause_name_def] >>

   CONJ_TAC >| [
     (* show not that the copied in scope is well typed and it doesn't include stars vars*)
     (* first show that the arguments are indeed well formed.*)
     gvs[] >>
     IMP_RES_TAC copyin_imp_wf_args2 >>

     gvs[map_simp_2] >>
     `ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) =
     ALL_DISTINCT (MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list))` by METIS_TAC[map_simp_2] >>
     gvs[] >>

     (* then use the abstract definition of copyin *)
     IMP_RES_TAC copyin_eq >>
     gvs[] >>

     (* now we know that the domain of the copyin consist only of var names not stars*)
     ASSUME_TAC copyin_abstract_domain >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
	  `ZIP ((MAP (λ(e,x,d). d) e_x_d_list),
  	   ZIP ((MAP (λ(e,x,d). x) e_x_d_list) ,
  	   (MAP (λ(e,x,d). e) e_x_d_list)))`,
	  `scopest ⧺ gscope`, `scope'`])) >>

     rfs[] >>
     rfs[map_distrub] >>
     IMP_RES_TAC star_not_in_varn_list >>
     gvs[] >>

     (* now conditinoue to show that the copied in scope is well typed *)
     ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:e`` ,
                            ``:'b`` |-> ``:d``] CI_scope_list_typed)  >>
		       
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
          `e_x_d_list`, `scopest`, `t_scope_list`, `gscope`,
	  `t_scope_list_g`, `scope'`, `e_tau_d_b_list`,
	  ` (order,f',delta_g,delta_b,delta_x,delta_t)`])) >>
    gvs[] >>
	
    METIS_TAC[map_simp_2, map_simp_3]
    ,

    Q.EXISTS_TAC `[(ZIP (mk_varn (MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list)),
                         MAP FST (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list)), stmt) ]` >>
    gvs[] >>
    REPEAT STRIP_TAC >>
    `i=0` by fs[] >>
    rw[] >>

    drule all_func_maps_contains_welltyped_body >>
    srw_tac [SatisfySimps.SATISFY_ss] []
   ]

 ,


 (*second subgoal of frame creation part *) 
 (* type frame with IH usage *)

 subgoal `i < LENGTH e_e'_x_d_list` >- (
 IMP_RES_TAC unred_arg_index_in_range >>
 METIS_TAC[LENGTH_MAP] ) >>


 subgoal `i < LENGTH e_tau_d_b_list` >- (
 IMP_RES_TAC unred_arg_index_in_range >>
 METIS_TAC[LENGTH_MAP] ) >>
 RES_TAC >>



 (*for the ith argument, it indeed preserves the type *)
 subgoal `sr_exp (EL i (MAP (λ(e_,e'_,x_,d_). e_) e_e'_x_d_list)) ty`  >- (
 fs[sr_exp_list_def] >>
 IMP_RES_TAC unred_arg_index_in_range >>
 IMP_RES_TAC EL_MEM >>
 RES_TAC ) >>

 rw[] >>

 ASSUME_TAC e_resulted_frame_is_WT >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
  `(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)`,
  `gscope`,
  `scopest`,
  `(EL i (MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list : (e # tau # d # bool) list ) ) )`,
  `e''`,
  `f_called`,`stmt_called`,`copied_in_scope`,
  `t_scope_list_g`,`t_scope_list`,
  `order`,
  `delta_g`,`delta_b`,`delta_x`,`delta_t`,
  `f'`, `Prs_n`, `ty`,
  `(EL i (MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list : (e # tau # d # bool) list )   ))`,
  `t_tau (EL i (MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (e # tau # d # bool) list ) ))`
  ])) >>
 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]


 ] 
]

,

(****************)
(*  select      *)
(****************)

REPEAT STRIP_TAC >>
SIMP_TAC list_ss [sr_exp_def] >>
REPEAT STRIP_TAC >|[



 OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 fs[] >| [

(*e_sel v*)

   rw[] >>
   OPEN_EXP_TYP_TAC ``(e_select (e_v v) l s)`` >>
   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   rfs[clause_name_def] >>
   OPEN_EXP_TYP_TAC ``(e_v v)`` >>
   rfs[clause_name_def] >> rw[] >>
   SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
   rfs[clause_name_def] >>

   SIMP_TAC (srw_ss()) [sel_def] >>
   Cases_on ` FIND (λ(ks,s). ks = v) l` >>
   fs[] >>
   fs[FIND_def] >>
   PairCases_on `z` >>
   fs[] >>
   IMP_RES_TAC index_mem >>
   IMP_RES_TAC mem_fst_snd >>
   fs[ELIM_UNCURRY] >>
   EVAL_TAC >>
   rw[]
   ,

   (*e_sel e*)

   rw[] >>
   OPEN_EXP_TYP_TAC ``(e_select (e) l s)`` >>
   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   rfs[clause_name_def] >>
   gvs[] >>

   Q.PAT_X_ASSUM `sr_exp e ty`
   ((STRIP_ASSUME_TAC o (Q.SPECL
   [`e'''`,
   `gscope`,
   `scopest`,
   `framel`,
   `t_scope_list`,
   `t_scope_list_g`,
   `t_tau tau'`,
   `b'`,
   `c`,
   `order`,
   `delta_g`,
   `delta_b`,
   `delta_t`,
   `delta_x`,
   `f` ])) o
   SIMP_RULE (srw_ss()) [sr_exp_def]) >> gvs[] >>


   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`f`,
   `stmt`,
   `s'`,
   `fr`])) >>
   fs[clause_name_def] >>

   Q.EXISTS_TAC `tau'` >>
   Q.EXISTS_TAC `b'''` >>
   Q.EXISTS_TAC `b''` >>

   gvs[] 
 ]
,


 fs[] >>
 OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
 OPEN_EXP_TYP_TAC ``(e_select e l s)`` >>
 rfs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
 
]




,

(****************)
(*  struct      *)
(****************)

REPEAT STRIP_TAC >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
REPEAT STRIP_TAC >| [

(*e type *)

 OPEN_EXP_RED_TAC ``(e_struct l2)`` >>
 rfs[] >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 fs[] >>
 rw[] >| [

  (*e_eStruct*)

   fs[sr_strexp_list_def] >>
   OPEN_EXP_TYP_TAC ``(e_struct (MAP (λ(f_,e_,v_). (f_,e_)) f_e_v_list))`` >>
   gvs[] >>

   IMP_RES_TAC lemma_MAP8 >>
   rw[] >>

   IMP_RES_TAC ured_mem_length >>
   `i < LENGTH ( f_e_e'_list)` by METIS_TAC[LENGTH_MAP] >>

   `LENGTH f_e_e'_list = LENGTH f_e_tau_b_list` by IMP_RES_TAC MAP_EQ_EVERY2 >>

   subgoal `sr_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty ` >-
   (IMP_RES_TAC EL_MEM >>
    IMP_RES_TAC mem_el_map2 >>
    gvs[] ) >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   fs[clause_name_def] >> rw[] >>


   Q.PAT_X_ASSUM `sr_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty`
   ((STRIP_ASSUME_TAC o (Q.SPECL
   [`e''`,
    `gscope`,
    `scopest`,
    `framel`,
    `t_scope_list`,
    `t_scope_list_g`,
    `t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list: (string # e # tau # bool) list )  ))`,
    `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list: (string # e # tau # bool) list)  ))`,
    `c`,
    `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
    `f`, `f_called` , `stmt_called`,  `copied_in_scope`, `Prs_n` ])) o
    SIMP_RULE (srw_ss()) [sr_exp_def]) >>
   gvs[] >>

   RES_TAC >>


   Q.EXISTS_TAC ` ZIP ( MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list ,
                  ZIP ((MAP (λ(f_,e_,e'_). e'_) f_e_e'_list),
                  ZIP ((MAP (λ(f_,e_,tau_,b_). tau_) f_e_tau_b_list) ,
     (LUPDATE b' i  (MAP (λ(f_,e_,tau_,b_). b_) f_e_tau_b_list)))))` >>


   rw[map_distrub] >>
   IMP_RES_TAC lemma_MAP8 >>
   fs[]  >>
     rw[map_rw_quad] >>
     SIMP_TAC list_ss [map_rw1] >>
     SIMP_TAC list_ss [map_rw2] >>
     fs[] >>

     Cases_on `i=i'` >| [
       RES_TAC >>
       rw[] >>
       fs[EL_LUPDATE] >>
       fs[sr_exp_def] 
       ,
       fs[EL_LUPDATE] >>
       fs[sr_exp_def] >>
       RES_TAC
       ]

   
   
   ,

   (* reduction struct -> v*)

   fs[clause_name_def] >> rw[] >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   SIMP_TAC (srw_ss()) [Once v_typ_cases] >>

   OPEN_EXP_TYP_TAC ``(e_struct (MAP (λ(f_,e_,v_). (f_,e_)) f_e_v_list))`` >>
   fs[clause_name_def] >> rw[] >>


   Q.EXISTS_TAC ` ZIP ( (MAP (λ(f_,e_,v_). f_) f_e_v_list),
                  ZIP( (MAP (λ(f_,e_,v_). v_) f_e_v_list) ,
                       (MAP (λ(f_,e_,tau_,b_). (tau_)) f_e_tau_b_list)) )` >>

   IMP_RES_TAC lemma_MAP8 >>
   IMP_RES_TAC MAP_EQ_EVERY2 >>
   rw[map_distrub] >| [

     rw[lemma_MAP8] >>
     rw[map_tri_zip12] >>
     SIMP_TAC list_ss [map_rw1] >>
     fs[] 
     ,
     
     rw[map_rw_quad] >>
     SIMP_TAC list_ss [map_rw2] >>
     fs[]
     ,
     RES_TAC >>
     IMP_RES_TAC evl_types_vl_blist >>
     IMP_RES_TAC evl_types_vl_F >>
     RES_TAC >>
     fs[LENGTH_MAP]

   ]
 ]

,


  (* frame creation part *)

 fs[sr_strexp_list_def] >>
 OPEN_EXP_RED_TAC ``(e_struct l2)`` >>
 OPEN_EXP_TYP_TAC ``(e_struct l2)`` >>
 gvs[] >>


 IMP_RES_TAC ured_mem_length >>
 `i < LENGTH ( f_e_e'_list)` by METIS_TAC[LENGTH_MAP] >>
 `LENGTH f_e_e'_list = LENGTH f_e_tau_b_list` by fs[ MAP_EQ_EVERY2, lemma_MAP8] >>

 subgoal ` sr_exp ((EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list))) ty ` >-
 (IMP_RES_TAC EL_MEM >>
  IMP_RES_TAC mem_el_map2 >>
  gvs[] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`(EL i (MAP (λ(f_,e_,e'_). e_) (f_e_e'_list : (string # e # e) list)))`])) >>
  gvs[] ) >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i`])) >> 

 ASSUME_TAC e_resulted_frame_is_WT >>


 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`c`, `gscope`, `scopest`,
  `(EL i (MAP (λ(f_,e_,tau_,b_). e_)  (f_e_tau_b_list : (string # e # tau # bool) list)))`,
        `e''`, `f_called` , `stmt_called`, `copied_in_scope`,
	` t_scope_list_g`, `t_scope_list`,
	`order`,
	`delta_g`,
	`delta_b`,
	`delta_x`,
	`delta_t`, `f`, `Prs_n`, `ty`,
         `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
	 `(t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`])) >>

 gvs[] >>

 subgoal `(EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list)) =
          (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- 
 (ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:string``,
                         ``:'b`` |-> ``:e``,
			 ``: γ`` |-> ``:e``,
			 `` :δ`` |->  ``:tau``,
			 `` :ε`` |->  ``:bool``] lemma_MAP8)  >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`f_e_e'_list`, `f_e_tau_b_list `])) >>
  fs[ELIM_UNCURRY] >>
  gvs[] ) >>

 fsrw_tac [] []
]

,

(*****************)
(*    header     *)
(*****************)

(*Same proof as above.*)



REPEAT STRIP_TAC >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
REPEAT STRIP_TAC >| [

(*e type *)

 OPEN_EXP_RED_TAC ``(e_header b l2)`` >>
 rfs[] >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 fs[] >>
 rw[] >| [

  (*e_eHeader*)

   fs[sr_strexp_list_def] >>
   OPEN_EXP_TYP_TAC ``(e_header b (MAP (λ(f_,e_,e'_). (f_,e_)) f_e_e'_list))`` >>
   gvs[] >>

   IMP_RES_TAC lemma_MAP8 >>
   rw[] >>

   IMP_RES_TAC ured_mem_length >>
   `i < LENGTH ( f_e_e'_list)` by METIS_TAC[LENGTH_MAP] >>

   `LENGTH f_e_e'_list = LENGTH f_e_tau_b_list` by IMP_RES_TAC MAP_EQ_EVERY2 >>

   subgoal `sr_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty ` >-
   (IMP_RES_TAC EL_MEM >>
    IMP_RES_TAC mem_el_map2 >>
    gvs[] ) >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   fs[clause_name_def] >> rw[] >>


   Q.PAT_X_ASSUM `sr_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty`
   ((STRIP_ASSUME_TAC o (Q.SPECL
   [`e''`,
    `gscope`,
    `scopest`,
    `framel`,
    `t_scope_list`,
    `t_scope_list_g`,
    `t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list: (string # e # tau # bool) list )  ))`,
    `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list: (string # e # tau # bool) list)  ))`,
    `c`,
    `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
    `f`, `f_called` , `stmt_called`,  `copied_in_scope`, `Prs_n` ])) o
    SIMP_RULE (srw_ss()) [sr_exp_def]) >>
   gvs[] >>

   RES_TAC >>


   Q.EXISTS_TAC ` ZIP ( MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list ,
                  ZIP ((MAP (λ(f_,e_,e'_). e'_) f_e_e'_list),
                  ZIP ((MAP (λ(f_,e_,tau_,b_). tau_) f_e_tau_b_list) ,
     (LUPDATE b' i  (MAP (λ(f_,e_,tau_,b_). b_) f_e_tau_b_list)))))` >>


   
   rw[map_distrub] >>
   IMP_RES_TAC lemma_MAP8 >>
   fs[]  >>
     rw[map_rw_quad] >>
     SIMP_TAC list_ss [map_rw1] >>
     SIMP_TAC list_ss [map_rw2] >>
     fs[] >>

     Cases_on `i=i'` >| [
       RES_TAC >>
       rw[] >>
       fs[EL_LUPDATE] >>
       fs[sr_exp_def] 
       ,
       fs[EL_LUPDATE] >>
       fs[sr_exp_def] >>
       RES_TAC
       ]

   
   
   ,

   (* reduction struct -> v*)

   fs[clause_name_def] >> rw[] >>

   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   SIMP_TAC (srw_ss()) [Once v_typ_cases] >>

   OPEN_EXP_TYP_TAC ``(e_header b (MAP (λ(f_,e_,v_). (f_,e_)) f_e_v_list))`` >>
   fs[clause_name_def] >> rw[] >>


   Q.EXISTS_TAC ` ZIP ( (MAP (λ(f_,e_,v_). f_) f_e_v_list),
                  ZIP( (MAP (λ(f_,e_,v_). v_) f_e_v_list) ,
                       (MAP (λ(f_,e_,tau_,b_). (tau_)) f_e_tau_b_list)) )` >>

   IMP_RES_TAC lemma_MAP8 >>
   IMP_RES_TAC MAP_EQ_EVERY2 >>
   rw[map_distrub] >| [

     rw[lemma_MAP8] >>
     rw[map_tri_zip12] >>
     SIMP_TAC list_ss [map_rw1] >>
     fs[] 
     ,
     
     rw[map_rw_quad] >>
     SIMP_TAC list_ss [map_rw2] >>
     fs[]
     ,
     fs[Once v_typ_cases, clause_name_def]
     ,
     RES_TAC >>
     IMP_RES_TAC evl_types_vl_blist >>
     IMP_RES_TAC evl_types_vl_F >>
     RES_TAC >>
     fs[LENGTH_MAP]

   ]
] 
,


  (* frame creation part *)

 fs[sr_strexp_list_def] >>
 OPEN_EXP_RED_TAC ``(e_header b l2)`` >>
 OPEN_EXP_TYP_TAC ``(e_header b l2)`` >>
 gvs[] >>


 IMP_RES_TAC ured_mem_length >>
 `i < LENGTH ( f_e_e'_list)` by METIS_TAC[LENGTH_MAP] >>
 `LENGTH f_e_e'_list = LENGTH f_e_tau_b_list` by fs[ MAP_EQ_EVERY2, lemma_MAP8] >>

 subgoal ` sr_exp ((EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list))) ty ` >-
 (IMP_RES_TAC EL_MEM >>
  IMP_RES_TAC mem_el_map2 >>
  gvs[] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`(EL i (MAP (λ(f_,e_,e'_). e_) (f_e_e'_list : (string # e # e) list)))`])) >>
  gvs[] ) >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i`])) >> 

 ASSUME_TAC e_resulted_frame_is_WT >>


 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`c`, `gscope`, `scopest`,
  `(EL i (MAP (λ(f_,e_,tau_,b_). e_)  (f_e_tau_b_list : (string # e # tau # bool) list)))`,
        `e''`, `f_called` , `stmt_called`, `copied_in_scope`,
	` t_scope_list_g`, `t_scope_list`,
	`order`,
	`delta_g`,
	`delta_b`,
	`delta_x`,
	`delta_t`, `f`, `Prs_n`, `ty`,
         `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
	 `(t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`])) >>

 gvs[] >>

 subgoal `(EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list)) =
          (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- 
 (ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:string``,
                         ``:'b`` |-> ``:e``,
			 ``: γ`` |-> ``:e``,
			 `` :δ`` |->  ``:tau``,
			 `` :ε`` |->  ``:bool``] lemma_MAP8)  >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`f_e_e'_list`, `f_e_tau_b_list `])) >>
  fs[ELIM_UNCURRY] >>
  gvs[] ) >>

 fsrw_tac [] []
]


,

(**********************)
(* sr_strexp_list []  *)
(**********************)

fsrw_tac [] [sr_strexp_list_def]

,


(**********************)
(* sr_strexp_list     *)
(**********************)

fsrw_tac [] [sr_strexp_list_def, sr_strexp_tup_def] >>
REPEAT STRIP_TAC >>
PairCases_on `tup` >> fs[]

,

(**********************)
(* sr_strexp_tup      *)
(**********************)

fsrw_tac [] [sr_strexp_tup_def]

,

(**********************)
(* sr_exp_list []     *)
(**********************)

fsrw_tac [] [sr_exp_list_def]

,

(**********************)
(* sr_exp_list        *)
(**********************)

fsrw_tac [] [sr_exp_list_def] >>
REPEAT STRIP_TAC >>
fs[]
]
);














