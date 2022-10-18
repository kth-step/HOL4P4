open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
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
open alistTheory;



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
       (type_scopes_list (t_scope_list_g) (scope)) /\
       (type_scopes_list (t_scope_list) (scopest)) /\
       (tsl_check_star_member t_scope_list  ) /\
       (e_red c scope scopest e e' framel ) /\
       (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e) tau  b) ==>
       (?b'. (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e') tau  b')) 
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
 (*IMP_RES_TAC index_find_length >>*)
 cheat>>
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
   (*IMP_RES_TAC index_find_first >>*) cheat>>
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
Induct >>
REPEAT STRIP_TAC >>
(*IMP_RES_TAC EL_pair_list >>*) cheat >>
rw[] >>
fs [ELIM_UNCURRY] >>
EVAL_TAC >>
METIS_TAC[]
);


val  EL_simp2 =
prove (``
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(x_,v_,tau_). (x_,v_,tau_)) l) ==>
(r,t) = EL i (MAP (λ(x_,v_,tau_). (v_,tau_)) l) ``,
REPEAT STRIP_TAC >>
(*IMP_RES_TAC EL_pair_list >>*) cheat >>
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
NTAC 2 (
(*IMP_RES_TAC EL_pair_list >> rw[] >>*) cheat >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2) >>
(* rfs[EL_pair_list,EL_simp1,EL_simp2] >> *)
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






val index_mem = prove (``
!l P n v. INDEX_FIND 0 P l = SOME (n,v) ==> MEM v l
``,
Induct >|[
fs[INDEX_FIND_def] 
,
fs[]>>
rw[]>>
fs[INDEX_FIND_def] >>
Cases_on `P h` >|[
fs[]>>
rw[]
,
fs[]>>
rw[]>>
ASSUME_TAC P_hold_on_next>> 
Q.PAT_X_ASSUM `∀i l P m.
          INDEX_FIND (SUC i) P l = SOME m ⇔
          INDEX_FIND i P l = SOME (FST m − 1,SND m) ∧ 0 < FST m`
( STRIP_ASSUME_TAC o (Q.SPECL [`0`,`l`,`P`,`(n,v)`])) >>
gvs[GSYM ADD1]>> 
RES_TAC >>
fs[]
] ]
);


val mem_fst_snd = prove (``
!l m. MEM m l ==> MEM (SND m) (MAP SND l) /\ MEM (FST m) (MAP FST l) ``,
Induct >>
REPEAT STRIP_TAC >>
fs[]
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
        ( MAP (λ(f_,e_,e'_). (f_,e_)) l =
        MAP (λ(f_,e_,e'_). (f_,e_)) l') ==>
	(MAP (λ(f_,e_,e'_). (f_)) l =
        MAP (λ(f_,e_,e'_). (f_)) l') /\
	(MAP (λ(f_,e_,e'_). (e_)) l =
        MAP (λ(f_,e_,e'_). (e_)) l') ``,

cheat
);





val map_distrub = prove ( 
``!l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>

(MAP (\(a_,b_,c_). a_) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a_,b_,c_). b_) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a_,b_,c_). c_) (ZIP (l,ZIP (l',l''))) = l'' /\
MAP (\(a_,b_,c_). (a_,b_)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l') /\
MAP (\(a_,b_,c_). (a_,c_)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l'') 
)``,
rw[lambda_unzip_tri] >>
rw[lambda_12_unzip_tri] >>
rw[map_tri_zip12] >>
EVAL_TAC >>
fs [GSYM UNZIP_MAP] >>
fs[MAP_ZIP]
);





val map_rw = prove ( `` !l . (MAP (λ(f_,e_,e'_). (f_,e'_)) l = ZIP ( (MAP (λ(f_,e_,e'_). (f_)) l) , (MAP (λ(f_,e_,e'_). (e'_)) l))) ``,
Induct >>
REPEAT STRIP_TAC >>
fs [GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
);






val el_of_vl_def = Define `
  el_of_vl vl = MAP (\(v). (e_v v)) (vl)
`;


val vl_el_conv = prove( ``
! l l'.  (l = vl_of_el l')  /\ (is_consts l') ==>
 (l' = el_of_vl l) ``,
Induct_on `l` >>
Induct_on `l'` >>
REPEAT STRIP_TAC >>
fs[el_of_vl_def, vl_of_el_def] >>
rw[]>>
Cases_on `h`>>
fs[v_of_e_def, is_const_def, is_consts_def]
);





val ev_types_v = prove (``
! v tau t_scope_list_g t_scope_list T_e .
  e_typ (t_scope_list_g,t_scope_list) T_e (e_v v) (tau) F ==>
  v_typ (v) (tau) F ``,

REPEAT STRIP_TAC >>
OPEN_EXP_TYP_TAC ``e_v v`` >>
fs[] ) ;



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





val evl_types_vl = prove(``
!l l' i t_scope_list_g t_scope_list T_e.
(LENGTH l = LENGTH l') /\
(i<LENGTH l) /\
is_consts (l) /\
(e_typ (t_scope_list_g,t_scope_list) T_e
          (EL i l)
          (EL i l') F) ==>
v_typ (EL i (vl_of_el l)) (EL i l') F ``,

Induct_on `l` >>
Induct_on `l'` >>
fs[] >>
REPEAT STRIP_TAC >>

(*
`is_consts l ==> !i . ?v. EL i l = e_v v` by cheat



fs[]
`(EL i (vl_of_el l)) =(v)` by cheat
fs[]

*)

IMP_RES_TAC ev_types_v  >>

subgoal `
!l' i. i < LENGTH l' /\ is_consts (l') ==>
is_const (EL i (l')) ` >- (
REPEAT STRIP_TAC >>
fs[is_consts_def] >>
fs[is_const_def] >>
fs[EVERY_EL] ) >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(h'::l): (e list)`, `i`])) >>
fs[] >>
RES_TAC >>

Cases_on `EL i (h'::l)` >>
fs[is_consts_def] >>
fs[is_const_def] >>
fs[EVERY_EL] >>
rw[] >>


IMP_RES_TAC e_types_v  >>
gvs[]>>



fs[Once EL_compute] >>
CASE_TAC >| [
rw[] >>
fs[vl_of_el_def]
,

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`l'`,`(i:num)-1`])) >>
fs[] >>
fs[numeralTheory.numeral_pre, PRE_SUB1, PRE_SUC_EQ ,ADD1] >>
rw[] >>
Cases_on `i = 1` >>
fs[] >>
gvs [v_of_e_def] >>
RES_TAC >>
gvs [vl_of_el_def] >>

subgoal ` EL (i − 1) (HD l::TL l) = EL (PRE (i − 1)) (TL l)  ` >- (
`0 < i - 1` by fs[] >>
ASSUME_TAC EL_CONS >>
Q.PAT_X_ASSUM `∀n. 0 < n ⇒ ∀x l. EL n (x::l) = EL (PRE n) l`
( STRIP_ASSUME_TAC o (Q.SPECL [`i-1`])) >>
RES_TAC >>
fs[EL_CONS] ) >>

subgoal `(HD l::TL l) = l  ` >- (
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

Q.PAT_X_ASSUM ` ∀t_scope_list_g' t_scope_list' T_e'.
          e_typ (t_scope_list_g',t_scope_list') T_e' (EL (i − 2) (TL l))
            (EL (i − 1) l') F ⇒
          v_typ (EL (i − 1) (MAP (λe. THE (v_of_e e)) l)) (EL (i − 1) l') F `
( STRIP_ASSUME_TAC o (Q.SPECL [`t_scope_list_g`, `t_scope_list`, `T_e`])) >>	  

gvs [] >>

fs[EL_CONS] >>
fs[PRE_SUB1] 
]
);



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
 




(*******************************************************************)

(* create a relation between two scopes *)

(* Single scope similarity *)
val similar_def = Define `
similar R l1 l2 = LIST_REL (\x y . (R (SND x) (SND y) ) /\ (FST x = FST y) ) l1 l2 `;


(*list of scopes similarity*)
val similarl_def = Define `
similarl R ll1 ll2 = LIST_REL (\l1 l2 . similar R l1 l2  ) ll1 ll2 `;




(*
alternatively:

val similar_def = Define `
similar R l1 l2 = ! i .  (R (SND (EL i l1)) (SND (EL i l2))) /\ (FST (EL i l1)) (FST (EL i l2)) `;


val similarl_def = Define `
similarl R ll1 ll2 = LIST_REL (\l1 l2 . similar R l1 l2  ) ll1 ll2 `;



type_scope:
type_scope sc tc = similar (\ (v , o)  t.  v_typ v t F) (sc) (tc)

*)




val INDEX_FIND_EQ_SOME_0 = store_thm ("INDEX_FIND_EQ_SOME_0",
  ``!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))``,

cheat);




val R_ALOOKUP_NONE_scopes = prove (``
! R v x t sc tc.
 similar R tc sc ==>
((NONE = ALOOKUP sc x)  <=>
(NONE = ALOOKUP tc x ) )``,


Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw [ALOOKUP_MEM] >>


REPEAT STRIP_TAC >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs [similar_def] >>
rw[] >>

Q.PAT_X_ASSUM `∀R' x tc'.
          LIST_REL (λx y. R' (SND x) (SND y) ∧ FST x = FST y) tc' sc ⇒
          (ALOOKUP sc x = NONE ⇔ ALOOKUP tc' x = NONE)`
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`x`,`tc`])) >>
fs[similar_def,LIST_REL_def]

);





val R_ALOOKUP_scopes = prove (``
! R v x t sc tc.
( similar R tc sc /\
(SOME v = ALOOKUP sc x)   /\
(SOME t = ALOOKUP tc x ) ) ==>
(R t v)``,

Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw [ALOOKUP_MEM] >>
FULL_SIMP_TAC list_ss [ALOOKUP_def, ALOOKUP_MEM] >>

REPEAT STRIP_TAC >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs [similar_def] >>
rw[] >>

(*lastone*)
Cases_on `h'0 = x` >>
fs[] >>
rw[] >>

Q.PAT_X_ASSUM `! R' v' x' t' tc'.
          LIST_REL (λx y. R' (SND x) (SND y) ∧ FST x = FST y) tc' sc ∧
          SOME v' = ALOOKUP sc x' ∧ SOME t' = ALOOKUP tc' x' ⇒
          R' t' v'`
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`v`,`x`,`t`, `tc`])) >>
fs[similar_def,LIST_REL_def]
);









(*Done!!*)

val R_find_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = find_topmost_map tcl x)   /\
(SOME l2 = find_topmost_map scl x ) ) ==>
((similar R (SND l1) (SND l2)) /\ (FST l1 = FST l2) )``,


simp [find_topmost_map_def] >>
NTAC 7 STRIP_TAC>>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) scl` >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) tcl` >>

fs[]>>
rw[]>>

PairCases_on `l1` >>
PairCases_on `l2` >>

Cases_on`l10 = l20 ` >| [

(*lists equal*)

gvs[] >>

fs[similarl_def] >>
IMP_RES_TAC P_holds_on_curent >>
fs[]>>


Cases_on `ALOOKUP l21 x`>>
Cases_on `ALOOKUP l11 x`>>
fs[]>>
rw[]>>

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
rw [similar_def]

,

(*prove by contradiction*)
CCONTR_TAC >>
gvs[] >>


(*the property holds on both l11 and l21*)
fs[similarl_def] >>
IMP_RES_TAC P_holds_on_curent >>
fs[]>>


(*simplify all the lookup cases *)
Cases_on `ALOOKUP l21 x`>>
Cases_on `ALOOKUP l11 x`>>
fs[]>>
rw[]>>


(*show that the relation holds on both index l20 and l110 for both scl and tcl*)
fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
IMP_RES_TAC LIST_REL_MEM_IMP >>
IMP_RES_TAC prop_in_range >>
subgoal `similar R (EL l20 tcl) (EL l20 scl) /\ similar R (EL l10 tcl) (EL l10 scl)` >-
(fs[]>>
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



` l20 < l10 \/ l10 < l20` by fs[] >>


fs[similar_def,LIST_REL_def] >>
fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
IMP_RES_TAC LIST_REL_MEM_IMP >>
IMP_RES_TAC prop_in_range >>
RES_TAC >>

IMP_RES_TAC P_holds_on_curent >>
RES_TAC >>
fs[similar_def]>>
rw[]




,

fs[]
,

cheat
(*the proof is the same as subgoal 2*)

]
);







val R_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = topmost_map tcl x)   /\
(SOME l2 = topmost_map scl x ) ) ==>
(similar R l1 l2)``,


simp [topmost_map_def] >>
REPEAT STRIP_TAC>>

Cases_on `find_topmost_map scl x` >>
Cases_on `find_topmost_map tcl x` >>

fs[]>>
rw[]>>

PairCases_on `x'` >>
PairCases_on `x''` >>
gvs[]>>

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
REPEAT STRIP_TAC>>

Cases_on `topmost_map tcl x` >>
Cases_on `topmost_map scl x` >>

fs[]>>
rw[]>>



ASSUME_TAC R_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`R`, `x`, `x'`, `x''`, `scl`, `tcl`])) >>


gvs[] >>

Cases_on `ALOOKUP x'' x` >>
Cases_on `ALOOKUP x' x` >>
fs[]>>
rw[]>>

fs[] >>

IMP_RES_TAC  R_ALOOKUP_scopes >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`, `v`])) >>
fs[]


);








val varn_is_typed = prove (``
!t_scope_list_g sl t_scope_list gsl varn v tau T_e.
          type_scopes_list t_scope_list sl ∧
          type_scopes_list t_scope_list_g gsl ∧
          SOME v = lookup_vexp2 gsl sl varn ∧
          SOME tau = lookup_tau t_scope_list_g t_scope_list varn ==>
          v_typ v tau F
``,



fs[lookup_vexp2_def] >>
fs[lookup_tau_def] >>

REPEAT STRIP_TAC >>

Cases_on `lookup_map (gsl ⧺ sl) varn` >>
Cases_on `lookup_map (t_scope_list_g ⧺ t_scope_list) varn` >>
fs[]>>
rw[]>>

ASSUME_TAC R_lookup_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`type_scopes_list`])) >>









Cases_on `x` >>
gvs[]





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

FULL_SIMP_TAC list_ss [] >> 
fs [clause_name_def] >>
rw[] >|[
(*variable name not a star*)







SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
rename1 `v`












,
cheat
(* thm requires the typing context *)
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
 
subgoal `v_typ (EL q (MAP (λ(x_,v_,tau_). v_) x_v_tau_list))
              (EL q (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)) F ` >- (
 RES_TAC
) >>

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

subgoal `v_typ (EL q (MAP (λ(x_,v_,tau_). v_) x_v_tau_list))
              (EL q (MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)) F ` >- (
 RES_TAC
) >>

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
rw[Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >> rw[] >>
RES_TAC
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
SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def]  >>
RES_TAC
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


SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def] >>
RES_TAC >>

,
OPEN_EXP_TYP_TAC ``(e_v (v_bit bitv))`` >> fs[] >>
OPEN_V_TYP_TAC ``(v_bit bitv)`` >>  fs[] 
]

,

(*unop_un_plus*)
OPEN_EXP_TYP_TAC ``(e_unop unop_un_plus e)`` >>
OPEN_EXP_RED_TAC ``(e_unop unop_un_plus e)`` >>
FULL_SIMP_TAC list_ss [] >> rw[] >|[

SIMP_TAC (srw_ss()) [Once e_typ_cases] >> (*to simplify the goal*)
fs[] >>
Q.EXISTS_TAC `b'` >>
fs [clause_name_def] >>
RES_TAC 
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

SIMP_TAC std_ss [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_concat e e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >| [

OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
fs[] >>

Q.PAT_X_ASSUM `sr_exp e ty`
((STRIP_ASSUME_TAC o (Q.SPECL
[`e'''''`,`scope`, `scopest`, `framel`, `t_scope_list`, `t_scope_list_g`,`T_e`, `(tau_bit w1)`, `b'`, `c`])) o
SIMP_RULE (srw_ss()) [sr_exp_def]) >>
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
rw[] >>
Q.EXISTS_TAC `w1`>>
Q.EXISTS_TAC `w2'`>>
Q.EXISTS_TAC `b'`>>
Q.EXISTS_TAC `b''`>>
fs[] >>

fs[sr_exp_def] >>
RES_TAC 

,
rw[] >>
OPEN_EXP_TYP_TAC ``(e_concat (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
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

(****************)
(* slice         *)
(****************)

SIMP_TAC std_ss [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_slice e e' e'')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >| [
rw[] >>
OPEN_EXP_TYP_TAC ``(e_slice e'⁵' (e_v (v_bit bitv)) (e_v (v_bit bitv')))`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rfs[] >>

Q.PAT_X_ASSUM `sr_exp e ty`
((STRIP_ASSUME_TAC o (Q.SPECL
[`e'''''`,`scope`, `scopest`, `framel`, `t_scope_list`, `t_scope_list_g`,`T_e`, `(tau_bit w)`, `T`, `c`])) o
SIMP_RULE (srw_ss()) [sr_exp_def]) >>

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
OPEN_EXP_TYP_TAC ``(e_select (e_v e) l s)`` >>
SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
rfs[clause_name_def] >>
RES_TAC >>
METIS_TAC[]
]

,

(****************)
(*  struct      *)
(****************)

SIMP_TAC (srw_ss()) [sr_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_struct l2)`` >>
rfs[] >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
fs[] >>
rw[] >| [

(*e_eStruct*)

fs [sr_strexp_list_def] >>
OPEN_EXP_TYP_TAC ``(e_struct (MAP (λ(f_,e_,v_). (f_,e_)) f_e_v_list))`` >>

IMP_RES_TAC ured_mem_length >>
 `i < LENGTH ( f_e_e'_list)` by METIS_TAC[LENGTH_MAP] >>
IMP_RES_TAC  mem_el_map2 >>
IMP_RES_TAC EL_MEM >>
IMP_RES_TAC MAP_EQ_EVERY2 >>

RES_TAC >>

SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
fs[clause_name_def] >> rw[] >>

Q.EXISTS_TAC `
ZIP ( MAP (λ(f_,e_,tau_). f_) f_e_tau_list ,
     ZIP ((MAP (λ(f_,e_,e'_). e'_) f_e_e'_list),
     MAP (λ(f_,e_,tau_). tau_) f_e_tau_list ))` >>


rw[map_distrub] >>
rw[lemma_MAP5] >>
rw [map_tri_zip12] >>
SIMP_TAC list_ss [map_rw] >>
fs[] >>
IMP_RES_TAC lemma_MAP5 >>
fs[]  >| [


rw[map_distrub] >>
rw[lemma_MAP5] >>
rw [map_tri_zip12] >>
SIMP_TAC list_ss [map_rw] >>
fs[] >>
IMP_RES_TAC lemma_MAP5 >>
fs[]

,


rw[map_distrub] >>
rw[lemma_MAP5] >>
rw [map_tri_zip12] >>
SIMP_TAC list_ss [map_rw] >>
fs[] >>
IMP_RES_TAC lemma_MAP5 >>
fs[]

,


rw[map_distrub] >>
rw[lemma_MAP5] >>
rw [map_tri_zip12] >>
SIMP_TAC list_ss [map_rw] >>
fs[] >>
IMP_RES_TAC lemma_MAP5 >>
fs[] >>

RES_TAC >>
(subgoal `e_typ (t_scope_list_g,t_scope_list) T_e
              (EL i' (MAP (λ(f_,e_,tau_). e_) f_e_tau_list))
              (EL i' (MAP (λ(f_,e_,tau_). tau_) f_e_tau_list)) F` ) >-
	      (RES_TAC ) >>
 

Cases_on `i=i'` >| [
RES_TAC >>
rw[] >>

PAT_ASSUM `` ∀e._``
( STRIP_ASSUME_TAC o (Q.SPECL [`EL i (MAP (λ(f_,e_,e'_). e_) (f_e_tau_list:(string # e # tau) list))`])) >>

rw[] >>

IMP_RES_TAC ured_mem_length >>
IMP_RES_TAC  mem_el_map2 >>
IMP_RES_TAC EL_MEM >>
IMP_RES_TAC MAP_EQ_EVERY2 >>
rw[] >>
RES_TAC >>
(*`sr_exp (EL i (MAP (λ(f_,e_,e'_). e_) f_e_tau_list)) ty` by fs[ELIM_UNCURRY] >> *)
RES_TAC >>
EVAL_TAC >>
fs[EL_LUPDATE] >>
fs [sr_exp_def] >>
RES_TAC
,
fs[EL_LUPDATE] >>
fs [sr_exp_def] >>
RES_TAC
]

]
,


(******************************************************************)
(*struct -> v*)

fs[clause_name_def] >> rw[] >>

SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
SIMP_TAC (srw_ss()) [Once v_typ_cases] >>

OPEN_EXP_TYP_TAC ``(e_struct (MAP (λ(f_,e_,v_). (f_,e_)) f_e_v_list))`` >>
fs[clause_name_def] >> rw[] >>


Q.EXISTS_TAC `
ZIP ( (MAP (λ(f_,e_,v_). f_) f_e_v_list),
   ZIP( (MAP (λ(f_,e_,v_). v_) f_e_v_list) , (MAP (λ(f_,e_,tau_). (tau_)) f_e_tau_list)  ))
` >>

IMP_RES_TAC MAP_EQ_EVERY2 >>
rw[map_distrub] >>
rw[lemma_MAP5] >>
rw [map_tri_zip12] >>
SIMP_TAC list_ss [map_rw] >>
fs[] >>
IMP_RES_TAC lemma_MAP5 >>
fs[] >>


RES_TAC >>
IMP_RES_TAC evl_types_vl >>
fs[LENGTH_MAP]

]


);


