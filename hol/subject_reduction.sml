open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory p4_auxTheory;
open deterTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open arithmeticTheory;



fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))

fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t exp_term (ta) bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))

(******   Subject Reduction for expression    ******)
val sr_exp_def = Define `
 sr_exp (e) (ty:'a itself) = ! e' scope scopest framel t_scope_list t_scope_list_g T_e tau b (c:'a ctx).
       (e_red c scope scopest e e' framel ) /\
       (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e) tau  b) ==>
       ((e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e') tau  b)) 
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
val sr_strexp_tuple_def = Define ` 
   sr_strexp_tup (tup : (string#e)) (ty:'a itself)
      =  sr_exp ((SND tup)) (ty:'a itself)
`;



(*
val sr_strexp_list_def = Define `
   sr_strexp_list (l : (string#v) list) (ty:'a itself)
      = !  (v:v) . MEM v (SND (UNZIP l)) ==> sr_exp(e_v(v)) (ty:'a itself)
`;

val sr_strexp_tuple_def = Define ` 
   sr_strexp_tup (tup : (string#v)) (ty:'a itself)
      =  sr_exp (e_v (SND tup)) (ty:'a itself)
`;
*)


(*************** Lemmas  ***************)

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
Cases_on `bitv`>>
Cases_on `bitv'`>>
Cases_on `bitv''` >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
);



(*
 If the property P holds on one list member in index i, then the index is
 indeed within the range of the list
*)
val prop_in_range =
prove(``
 !l P i f. ( INDEX_FIND 0 P l = SOME (i,f)) ==> (i < LENGTH l ) ``,
 REPEAT STRIP_TAC >>
 Cases_on `INDEX_FIND 0 P l = SOME (i,f)` >> 
 fs [] >>
 IMP_RES_TAC index_find_length >>
 fs []
);



(*
 P should hold on the member it finds.
*)
val P_holds_on_curent = prove(``
  !l P i m. INDEX_FIND i P l = SOME m  ==>
  P (SND m) ``,
  Induct_on `l` >>
  fs [INDEX_FIND_def] >>
  NTAC 2 GEN_TAC >>
  CASE_TAC >>
  rw []
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
rw [] >>
fs[INDEX_FIND_def] 
);



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
rw [] >>
fs[INDEX_FIND_def]
);




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
   (*IMP_RES_TAC P_current_next_same >>*)
   rw[] >>
   SIMP_TAC arith_ss [Once EL_compute] >>
   CASE_TAC >>
   ASSUME_TAC P_hold_on_next >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
   gvs[GSYM ADD1]>> 
   rw[] >>
   IMP_RES_TAC P_holds_on_curent >>
   IMP_RES_TAC index_find_first >>
   rfs[] >>
   rw[] >>
   (*SIMP_TAC arith_ss [Once EL_compute] >>*)
   fs[
   numeralTheory.numeral_pre,
   arithmeticTheory.PRE_SUB1,
   arithmeticTheory.PRE_SUC_EQ
   ] >>
   fs[Once INDEX_FIND_add] >> 
   PairCases_on `z` >>
   rw [] >>
   fs[INDEX_FIND_def] >>
     rw[] >>
     RES_TAC>>
     fs[] >>
     rw[] 
]);





val EL_relation_to_INDEX_less =
prove (``
!l P i m n. INDEX_FIND 0 P l = SOME (i,n) /\ EL i l  = (m) /\
i < LENGTH l ==>
m = n``,
`!l i. i < LENGTH l ==> i <= LENGTH l ` by FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
RES_TAC >>
IMP_RES_TAC EL_relation_to_INDEX_lesseq
 );



val  EL_simp1 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
(q) = EL i (MAP (λ(x_,v_,tau_). (x_)) l) ``,
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_pair_list >>
rw[] >>
fs [ELIM_UNCURRY] >>
METIS_TAC[]
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
fs [ELIM_UNCURRY] >>
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
NTAC 2 (IMP_RES_TAC EL_pair_list >> rw[] >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2) >>
rfs[EL_pair_list,EL_simp1,EL_simp2] >>
fs [ELIM_UNCURRY] >>
rfs[] >>
rfs[MAP_MAP_o] >>
METIS_TAC[]
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

REPEAT STRIP_TAC>>
rfs[EL_pair_list,EL_simp1,EL_simp2] >>
fs [ELIM_UNCURRY] >>
rfs[] >>
rfs[Once MAP_o] >>
EVAL_TAC>>
AP_TERM_TAC >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND]>>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
METIS_TAC []
);


val EL_simp_exist1 =
prove (``
!l i q r .
 i<LENGTH l /\
(q,r) = EL i (MAP (λ(x_,v_,tau_). (x_,v_)) l) ==>
?t . (t) = EL i (MAP (λ(x_,v_,tau_). (tau_)) l) ``,
REPEAT STRIP_TAC>>
rfs[EL_pair_list,EL_simp1,EL_simp2] );




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
  fs [ELIM_UNCURRY] >>
  rfs[] 
  ,
  fs[] >>
  FULL_SIMP_TAC list_ss [] >>
  Cases_on `(λ(k,v). k = q') ((λ(x_,v_,tau_). (x_,tau_)) h)` >|[
   fs[] >>
   fs [ELIM_UNCURRY]
   ,
   REPEAT(
   rfs[REWRITE_RULE [GSYM ONE] (SPEC ``0`` (P_hold_on_next))] >>
   ASSUME_TAC P_hold_on_next>>
   IMP_RES_TAC P_implies_next >>
   IMP_RES_TAC P_current_next_same >>
   RES_TAC >>
   rfs[] >>	
   SIMP_TAC arith_ss [Once EL_compute] >>
   fs[
   numeralTheory.numeral_pre,
   arithmeticTheory.PRE_SUB1,
   arithmeticTheory.PRE_SUC_EQ
   ] >>
   rw[] >>
   fs[
   numeralTheory.numeral_pre,
   arithmeticTheory.PRE_SUB1,
   arithmeticTheory.PRE_SUC_EQ
   ] >>
   RES_TAC >>
   fs[] )
   ]
]
);




val correct_field_index_lemma = prove (``
! (l:(string#v#tau)list ) i q r tau .
INDEX_FIND 0 (λ(k,v). k = q) (MAP (λ(x_,v_,tau_). (x_,v_)) l) = SOME (i,
EL i (MAP (λ(x_,v_,tau_). (x_,v_)) l))
   /\
correct_field_type (MAP (λ(x_,v_,tau_). (x_,tau_)) l) q
          tau
  /\
(q,r) = EL i (MAP (λ(x_,v_,tau_). (x_,v_)) l)  
      ==>
         tau = EL i (MAP (λ(x_,v_,tau_). tau_) l)``,

REPEAT STRIP_TAC >>
rfs[correct_field_type_def] >>
rfs[tau_in_rec_def] >>
Cases_on `FIND (λ(xm,tm). xm = q) (MAP (λ(x_,v_,tau_). (x_,tau_)) l)` >>
fs[FIND_def] >>
PairCases_on `z` >>
rw[] >>
Cases_on `SND (z0,z1,z2)` >>
fs[] >>
rw[] >> 

Cases_on `r' = tau`>>
fs[] >>
rw[] >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs [ELIM_UNCURRY]>>
`INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,EL i (MAP (λx. (FST x,FST (SND x))) l)) ==>
INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,q,r)
` by METIS_TAC[] >>
RES_TAC >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs [ELIM_UNCURRY]
);



val SR_e =
prove (`` ! (ty:'a itself) .
(!e. sr_exp e ty) /\
(! (l1: e list). sr_exp_list l1 ty) /\
(! (l2: (string#e) list) .  sr_strexp_list l2 ty) /\
(! tup. det_strexp_tup tup ty)   ``,

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
FULL_SIMP_TAC list_ss [] >> rw[] >|[
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
cheat
,
cheat
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

fs [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_acc e s)`` >>
FULL_SIMP_TAC list_ss [lemma_v_red_forall] >> rw[] >|[


OPEN_EXP_TYP_TAC ``(e_acc (e_v (v_struct f_v_list)) s)`` >>
rw[] >>
OPEN_EXP_TYP_TAC ``(e_v (v_struct f_v_list))`` >>
rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rw[] >>
OPEN_V_TYP_TAC ``(v_struct f_v_list)`` >>
rw[] >>
fs [clause_name_def]  >>
rw []>>

rfs[FIND_def, MEM_EXISTS] >>
Cases_on `z` >>
Cases_on `r` >>
IMP_RES_TAC prop_in_range >>
fs[LENGTH_MAP] >>
RES_TAC >>
rw[] >>

IMP_RES_TAC EL_relation_to_INDEX_less >>
fs[LENGTH_MAP] >>
RES_TAC>>
rw[]>>
IMP_RES_TAC EL_simp5 >>
(*dont rewrite here*)
IMP_RES_TAC correct_field_index_lemma >>
rfs[]

,

(*e_acc_arg1*)

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
fs [clause_name_def]  >>
rw []>>

rfs[FIND_def, MEM_EXISTS] >>
Cases_on `z` >>
Cases_on `r` >>
IMP_RES_TAC prop_in_range >>
fs[LENGTH_MAP] >>
RES_TAC >>
rw[] >>

IMP_RES_TAC EL_relation_to_INDEX_less >>
fs[LENGTH_MAP] >>
RES_TAC>>
rw[]>>
IMP_RES_TAC EL_simp5 >>
(*dont rewrite here*)
IMP_RES_TAC correct_field_index_lemma >>
rfs[]

]




,
(*****************)
(*  unary oper   *)
(*****************)

REPEAT STRIP_TAC >>
fs [sr_exp_def] >>
Cases_on `u` >>
REPEAT STRIP_TAC >|[

(*unop_neg*)
OPEN_EXP_RED_TAC ``(e_unop u e)`` >>
OPEN_EXP_TYP_TAC ``e_unop unop_neg e`` >>
FULL_SIMP_TAC list_ss [lemma_v_red_forall] >> rw[] >|[

(*e*)
RES_TAC >>
rw[Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >> rw[]
,

(*v*)
OPEN_EXP_TYP_TAC ``(e_v (v_bool b'))`` >>
fs[] >>
OPEN_V_TYP_TAC ``(v_bool _)`` >>
fs [] 
]

,


(*unop_compl*)
OPEN_EXP_TYP_TAC ``e_unop unop_compl e`` >>
OPEN_EXP_RED_TAC ``e_unop unop_compl e`` >>
FULL_SIMP_TAC list_ss [] >> rw[] >| [
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def] 
,

OPEN_EXP_TYP_TAC ``(e_v (v_bool b'))`` >>
fs[] >>
rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
OPEN_V_TYP_TAC ``(v_bit bitv)`` >>

fs [clause_name_def] >>
Cases_on `b'` >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
rw [clause_name_def, bs_width_def] >>
Cases_on `bitv` >>
FULL_SIMP_TAC std_ss [bs_width_def, bitv_bl_unop_def]
]
,

(*e_unop unop_neg_signed e*)

OPEN_EXP_TYP_TAC ``e_unop unop_neg_signed e`` >>
OPEN_EXP_RED_TAC ``e_unop unop_neg_signed e`` >>
FULL_SIMP_TAC list_ss [] >> rw[] >|[

RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def]
,
OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >> fs[] >>
OPEN_V_TYP_TAC ``(v_bit bitv)`` >>  fs[] 
]

,

(*unop_un_plus*)
OPEN_EXP_TYP_TAC ``(e_unop unop_un_plus e)`` >>
OPEN_EXP_RED_TAC ``(e_unop unop_un_plus e)`` >>
FULL_SIMP_TAC list_ss [] >> rw[] >|[
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def]
,
OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >> rfs[] >>
OPEN_V_TYP_TAC ``(v_bit bitv)`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >> fs[]
]
]

,

(****************)
(*  binop       *)
(****************)

fs [sr_exp_def] >>
REPEAT STRIP_TAC  >>
Cases_on `b` >| [
(*this section  works from mul to shr  so first 7 cases +(and+oxor+or) *)

OPEN_EXP_RED_TAC ``(e_binop e _ e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] >>
OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> 
rfs[is_bool_op_def, is_bv_bool_op_def, is_bv_op_def] >> rw[] >| [

RES_TAC >>
fs[] >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]

,

OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >>
OPEN_EXP_TYP_TAC `` (e_v (v_bit bitv))`` >>
FULL_SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
Cases_on `bitv` >>
Cases_on `bitv'` >>
TRY (Cases_on `bitv''`) >>
rw[] >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma 
]

,

(*shr till gt + xor  so the nest 4 cases *)

OPEN_EXP_RED_TAC ``(e_binop e _ e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] >>
OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> 
rfs[is_bool_op_def, is_bv_bool_op_def, is_bv_op_def] >> rw[] >| [

RES_TAC >>
fs[] >>
TRY (Q.EXISTS_TAC `w`) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY (Q.EXISTS_TAC `w`) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY (Q.EXISTS_TAC `w`) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]

,

OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv'))`` >>
OPEN_EXP_TYP_TAC `` (e_v (v_bit bitv))`` >>
FULL_SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
Cases_on `bitv` >>
Cases_on `bitv'` >>
TRY (Cases_on `bitv''`) >>
rw[] >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma>>
rfs[clause_name_def]
]


,



(*eq+neq*)

OPEN_EXP_RED_TAC ``(e_binop e _ e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] >>
OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> 
rfs[is_bool_op_def, is_bv_bool_op_def, is_bv_op_def] >>
rw[] >>
rfs[clause_name_def] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
rfs[clause_name_def] >| [

RES_TAC >>
fs[] >>
TRY(DISJ1_TAC) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY(DISJ2_TAC) >>
TRY (Q.EXISTS_TAC `w`) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY(DISJ1_TAC) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
,
RES_TAC >>
fs[] >>
TRY(DISJ2_TAC) >>
TRY (Q.EXISTS_TAC `w`) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def]
]


,
(*and or go back up ... here only binop_bin_and *)

OPEN_EXP_RED_TAC ``(e_binop e _ e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] >>
OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> 
rfs[is_bool_op_def, is_bv_bool_op_def, is_bv_op_def] >>
rw[] >>
rfs[clause_name_def] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
rfs[clause_name_def] >>

(*first three goals *)
RES_TAC >>
fs[] >>
TRY(DISJ1_TAC) >>
TRY (
Q.EXISTS_TAC `b` >>
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def] >>


(*fourth goal*)

RES_TAC >>
fs[] >>
TRY(DISJ1_TAC) >>
TRY (
Q.EXISTS_TAC `b` >>   
Q.EXISTS_TAC `b''`) >> rfs[clause_name_def] >>
OPEN_EXP_TYP_TAC ``(e_v (v_bool T))`` >> fs[] >>
OPEN_EXP_TYP_TAC ``e'`` >> fs[] >>
OPEN_V_TYP_TAC ``(v_bool T)`` >>
fs[] >> rfs[clause_name_def] >> rw[]
fs[lemma_v_red_forall]

cheat





]



,

(****************)
(*  concat      *)
(****************)
REPEAT STRIP_TAC >>
fs [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_concat e e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >| [

OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
fs[] >>
RES_TAC >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rw[] >>
Q.EXISTS_TAC `w1`>>
Q.EXISTS_TAC `w2'`>>
Q.EXISTS_TAC `b'`>>
Q.EXISTS_TAC `b''`>>
fs[]

,

rw[] >>
OPEN_EXP_TYP_TAC ``(e_concat (e_v (v_bit bitv)) e')`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
RES_TAC >>
rw[] >>
Q.EXISTS_TAC `w1`>>
Q.EXISTS_TAC `w2'`>>
Q.EXISTS_TAC `b'`>>
Q.EXISTS_TAC `b''`>>
fs[] 
,
rw[] >>
OPEN_EXP_TYP_TAC ``(e_concat (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>
OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>
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

(****************)
(* slice         *)
(****************)

fs [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_slice e e' e'')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >| [
rw[] >>
OPEN_EXP_TYP_TAC ``(e_slice e'⁵' (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rfs[] >>
RES_TAC >>
Q.EXISTS_TAC `w`>>
rfs[]
,
rw[] >>
OPEN_EXP_TYP_TAC ``(e_slice (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rfs[] >>
RES_TAC >>
rfs[] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
FULL_SIMP_TAC (srw_ss()) [lemma_v_red_forall] >>
FULL_SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
(*OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >>*)
rfs[] >>
OPEN_V_TYP_TAC ``(v_bit bitv)`` >>
rfs[]
]

,

(****************)
(*  call        *)
(****************)


fs [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_call f l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >| [
OPEN_EXP_TYP_TAC ``(e_call f (MAP (λ(e_,x_,d_). e_) e_x_d_list))`` >>
fs[] >>
rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
cheat
,

Q.EXISTS_TAC `e_tau_d_b_list`
REPEAT STRIP_TAC >>
cheat
]

,
(****************)
(*  select      *)
(****************)

fs [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >|[
rw[] >>
OPEN_EXP_TYP_TAC ``(e_select (e_v v) l s)`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rfs[] >>
rfs[clause_name_def] >> 
OPEN_EXP_TYP_TAC ``(e_v v)`` >>
rfs[clause_name_def] >> rw[] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>

Cases_on `LENGTH l`

RES_TAC >>
Q.EXISTS_TAC `w`>>
rfs[]


,


]



]
);



