
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
open intLib;



fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))


fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t ^exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))



val Fb_star_defined_def = Define `
Fb_star_defined (b_func_map:b_func_map) (t_scope_list_g:t_scope_list_g) =
! x . (is_lookup_defined b_func_map x)
             <=>
      (is_lookup_defined (EL 0 t_scope_list_g) (varn_star (funn_name x)))
`;







val prog_exp_def = Define `
 prog_exp (e) (ty:'a itself) =
 !gscope (scopest:scope list) t_scope_list t_scope_list_g
 T_e tau b (c:'a ctx) order delta_g delta_b (delta_t:delta_t) delta_x f.
     	 
          type_scopes_list gscope t_scope_list_g ∧
          type_scopes_list scopest t_scope_list ∧
	  star_not_in_sl (scopest) ∧
	  ~(is_const e) ∧
          e_typ (t_scope_list_g,t_scope_list) T_e e tau b ∧
          (T_e = (order,  f, (delta_g, delta_b, delta_x, delta_t))) /\	  
	  WT_c c order t_scope_list_g delta_g delta_b delta_x ==>
          ?e' framel. e_red c gscope scopest e e' framel
`;




(****** Type progress for expression list ******)
val prog_exp_list_def = Define `
 prog_exp_list (l : e list) (ty:'a itself) = 
       !(e : e). MEM e l ==> prog_exp (e) (ty:'a itself)
`;


(****** Type progress for strexp list ******)
val prog_strexp_list_def = Define `
   prog_strexp_list (l : (string#e) list) (ty:'a itself)
      = !  (e:e) . MEM e (SND (UNZIP l)) ==> prog_exp(e) (ty:'a itself)
`;


(****** Type progress for str e tup list ******)
val prog_strexp_tup_def = Define ` 
   prog_strexp_tup (tup : (string#e)) (ty:'a itself)
      =  prog_exp ((SND tup)) (ty:'a itself)
`;




(************************************************************)
val INDEX_FIND_EQ_SOME_0 = store_thm ("INDEX_FIND_EQ_SOME_0",
  ``!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))``,

cheat);

val P_NONE_hold = prove ( ``
!P l n .  (INDEX_FIND 0 P l = NONE) ==> (INDEX_FIND n P l = NONE) `` ,
 cheat 
);

val P_NONE_hold2 = prove ( ``
!P l n .  (INDEX_FIND n P l = NONE) ==> (INDEX_FIND 0 P l = NONE) `` ,
 cheat
);

val R_ALOOKUP_NONE_scopes = prove (``
! R v x t sc tc.
 similar R tc sc ==>
((NONE = ALOOKUP sc x)  <=>
(NONE = ALOOKUP tc x ) )``,
cheat
);



val lemma_v_red_forall = prove ( ``
! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl ``, cheat);



val R_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = topmost_map tcl x)   /\
(SOME l2 = topmost_map scl x ) ) ==>
(similar R l1 l2)``,
cheat
);

val R_find_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = find_topmost_map tcl x)   /\
(SOME l2 = find_topmost_map scl x ) ) ==>
((similar R (SND l1) (SND l2)) /\ (FST l1 = FST l2) )``,
cheat);



val P_current_next_same = prove (``
    !l P m n. INDEX_FIND 0 P l = SOME m /\
              INDEX_FIND 1 P l = SOME n ==> SND n = SND m
``,
cheat
);



val P_implies_next = prove (``
    !l P i m. INDEX_FIND 0 P l = SOME (i, m) ==>
              INDEX_FIND 1 P l = SOME (SUC i, m)
``,
cheat
);



val not_index_none_exist =
prove(``
∀ l n P. ~ (INDEX_FIND n P l = NONE) ⇔ EXISTS P l ``,
cheat
);




val UNZIP_rw = prove(`` !l l'.
(FST (UNZIP (MAP (\(a_,b_,c_). (a_,b_)) l)) = MAP (\(a_,b_,c_). (a_)) l) /\
(FST (UNZIP (MAP (\(a_,b_,c_). (b_,c_)) l)) = MAP (\(a_,b_,c_). (b_)) l) /\
(FST (UNZIP (MAP (\(a_,b_,c_). (a_,c_)) l)) = MAP (\(a_,b_,c_). (a_)) l) /\
(SND (UNZIP (MAP (\(a_,b_,c_). (a_,b_)) l)) = MAP (\(a_,b_,c_). (b_)) l) /\
(SND (UNZIP (MAP (\(a_,b_,c_). (b_,c_)) l)) = MAP (\(a_,b_,c_). (c_)) l) /\
(SND (UNZIP (MAP (\(a_,b_,c_). (a_,c_)) l)) = MAP (\(a_,b_,c_). (c_)) l) /\


(FST (UNZIP (MAP (\(a_,b_,c_,d_). (a_,b_)) l')) = MAP (\(a_,b_,c_,d_). (a_)) l') /\
(FST (UNZIP (MAP (\(a_,b_,c_,d_). (a_,c_)) l')) = MAP (\(a_,b_,c_,d_). (a_)) l') /\
(FST (UNZIP (MAP (\(a_,b_,c_,d_). (a_,d_)) l')) = MAP (\(a_,b_,c_,d_). (a_)) l') /\
(FST (UNZIP (MAP (\(a_,b_,c_,d_). (b_,c_)) l')) = MAP (\(a_,b_,c_,d_). (b_)) l') /\
(FST (UNZIP (MAP (\(a_,b_,c_,d_). (b_,d_)) l')) = MAP (\(a_,b_,c_,d_). (b_)) l') /\
(FST (UNZIP (MAP (\(a_,b_,c_,d_). (c_,d_)) l')) = MAP (\(a_,b_,c_,d_). (c_)) l') /\

(SND (UNZIP (MAP (\(a_,b_,c_,d_). (a_,b_)) l')) = MAP (\(a_,b_,c_,d_). (b_)) l') /\
(SND (UNZIP (MAP (\(a_,b_,c_,d_). (a_,c_)) l')) = MAP (\(a_,b_,c_,d_). (c_)) l') /\
(SND (UNZIP (MAP (\(a_,b_,c_,d_). (a_,d_)) l')) = MAP (\(a_,b_,c_,d_). (d_)) l') /\
(SND (UNZIP (MAP (\(a_,b_,c_,d_). (b_,c_)) l')) = MAP (\(a_,b_,c_,d_). (c_)) l') /\
(SND (UNZIP (MAP (\(a_,b_,c_,d_). (b_,d_)) l')) = MAP (\(a_,b_,c_,d_). (d_)) l') /\
(SND (UNZIP (MAP (\(a_,b_,c_,d_). (c_,d_)) l')) = MAP (\(a_,b_,c_,d_). (d_)) l') 
``, cheat);




val R_lookup_map_scopesl = prove (``
! R v x t scl tcl.
( similarl R tcl scl /\
(SOME v = lookup_map scl x)   /\
(SOME t = lookup_map tcl x ) ) ==>
(R t v)``,
cheat);


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

LAST_X_ASSUM
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`v`,`x`,`t`, `tc`])) >>
fs[similar_def,LIST_REL_def]
);




val R_ALOOKUP_scopes = prove (``
! R v x t sc tc.
( similar R tc sc /\
(SOME v = ALOOKUP sc x)   /\
(SOME t = ALOOKUP tc x ) ) ==>
(R t v)``,
cheat
);



val type_scopes_list_APPEND = prove (``
! l1 l2 l3 l4. type_scopes_list l1 l2 /\
          type_scopes_list l3 l4 ==>
	  type_scopes_list (l1++l3) (l2++l4)``,
cheat
);




val lookup_in_gsl_lemma = prove ( ``
! v f sl gsl.
SOME v = lookup_vexp2 sl gsl (varn_star f) /\
star_not_in_sl sl ==>
SOME v = lookup_vexp2 [] gsl (varn_star f)   `` ,
cheat
);


val lookup_map_in_gsl_lemma  = prove ( ``
! v lvalop f sl gsl.
SOME (v,lvalop)  = lookup_map (sl ⧺ gsl) (varn_star f) /\
star_not_in_sl sl ==>
SOME (v,lvalop) = lookup_map   gsl (varn_star f)
``,
cheat);



val EL_consts_is_const = prove (``
!l i. i < LENGTH l /\ is_consts (l) ==>
is_const (EL i (l)) `` ,
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
cheat
);



val map_rw_quad = prove ( ``
!l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>
(MAP (\(a_,b_,c_,d_). a_) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a_,b_,c_,d_). b_) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a_,b_,c_,d_). c_) (ZIP (l,ZIP (l',l''))) = FST (UNZIP l'') /\
MAP (\(a_,b_,c_,d_). d_) (ZIP (l,ZIP (l',l''))) = SND (UNZIP l'') /\
MAP (\(a_,b_,c_,d_). (a_,b_)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l')  /\
MAP (\(a_,b_,c_,d_). (a_,c_)) (ZIP (l,ZIP (l',l''))) = ZIP (l, FST (UNZIP l'') ) /\
MAP (\(a_,b_,c_,d_). (b_,c_)) (ZIP (l,ZIP (l',l''))) = ZIP (l', FST (UNZIP l'') )
)``, cheat);




val map_rw1 = prove ( ``
!l . (MAP (\(f_,e_,e'_). (f_,e'_)) l =
         ZIP (MAP (\(f_,e_,e'_). f_) l,MAP (\(f_,e_,e'_). e'_) l)) /\
     (MAP (\(f_,e_,e'_). (f_,e_)) l =
         ZIP (MAP (\(f_,e_,e'_). f_) l,MAP (\(f_,e_,e'_). e_) l))	 ``,
cheat
);


(************************************************************)



val INDEX_FIND_concat3 = prove (``
! P sl gsl.
INDEX_FIND 0 P (sl ⧺ gsl) = NONE <=>
(INDEX_FIND 0 P (sl) = NONE /\
INDEX_FIND 0 P (gsl) = NONE) ``,

rw[] >>
rpt strip_tac>>
fs[INDEX_FIND_NONE_EXISTS]
);



val find_topmost_map_concat_none = prove( ``
! sl gsl v .
find_topmost_map (sl ⧺ gsl) v = NONE <=>
(find_topmost_map (sl) v  = NONE /\
 find_topmost_map (gsl) v  = NONE )``,

rpt strip_tac >>
fs[find_topmost_map_def] >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc v)) (sl ⧺ gsl)` >>
fs[] >| [

IMP_RES_TAC INDEX_FIND_concat3 >>
gvs[]
,

Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc v)) sl` >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc v)) gsl` >>
gvs[] >>


IMP_RES_TAC INDEX_FIND_concat3 >>
gvs[]
]
);



val topmost_map_concat_none = prove ( ``
! sl gsl v .
topmost_map (sl ⧺ gsl) v = NONE <=>
(topmost_map (sl) v = NONE /\
 topmost_map (gsl) v = NONE ) ``,

rpt strip_tac >>
fs[topmost_map_def] >>
fs[] >>

Cases_on `find_topmost_map (sl ⧺ gsl) v`>>
fs[] >| [

IMP_RES_TAC find_topmost_map_concat_none >>
gvs[]
,

PairCases_on `x` >> fs[] >>
Cases_on `find_topmost_map sl v` >>
Cases_on `find_topmost_map gsl v` >>
fs[] >>
TRY (PairCases_on `x` >> fs[] ) >>

IMP_RES_TAC find_topmost_map_concat_none >>
gvs[]
]
);



val topmost_map_not_none = prove ( ``
! l v x .
topmost_map l v = SOME x ==>
~(ALOOKUP x v = NONE) ``,

fs[topmost_map_def] >>
fs[find_topmost_map_def] >>
REPEAT STRIP_TAC >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc v)) l` >>
fs[] >>
PairCases_on `x'` >> 
gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0]
);



val lookup_map_concat_none = prove ( ``
! sl gsl v .
lookup_map (sl ⧺ gsl) (v) = NONE <=>
(lookup_map (sl) (v) = NONE /\
 lookup_map (gsl) (v) = NONE) ``,

rpt strip_tac >>
fs[lookup_map_def] >>
fs[] >>

Cases_on `topmost_map (sl ⧺ gsl) v` >>
fs[] >| [
IMP_RES_TAC topmost_map_concat_none >>
gvs[]
,


Cases_on `topmost_map sl v` >>
Cases_on `topmost_map gsl v` >>
fs[] >>

IMP_RES_TAC topmost_map_concat_none >>
gvs[] >>

Cases_on `ALOOKUP x v` >>
Cases_on `ALOOKUP x' v`>>
gvs[] >>

IMP_RES_TAC topmost_map_not_none
]
);

val R_implies_ALOOKUP_scopes = prove (``
! R x v t sc tc.
 similar R tc sc ==>

(((SOME t = ALOOKUP tc x) ==>
(? v . SOME v = ALOOKUP sc x  /\ R t v )) /\
((SOME v = ALOOKUP sc x) ==>
(? t . SOME t = ALOOKUP tc x  /\ R t v )))
 ``,

Induct_on `tc` >>
Induct_on `sc` >>
fs[ALOOKUP_def, similar_def] >>

rpt strip_tac >| [
fs[similar_def] >>
PairCases_on `h` >>
PairCases_on `h'` >>
gvs[] >>
Cases_on `h'0 = x` >> fs[]
,


PairCases_on `h` >>
PairCases_on `h'` >>
gvs[] >>
fs[ALOOKUP_def, similar_def] >>
Cases_on `h'0 = x` >> fs[] >> gvs[] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`R`, `x`, `v`, `t'`, `sc`])) >> gvs[] >>
srw_tac [SatisfySimps.SATISFY_ss][]
]
);




val R_ALOOKUP_NONE_scopelist = prove (``
! R v x t scl tcl.
 similarl R tcl scl ==>
((NONE = find_topmost_map scl x)  <=>
(NONE = find_topmost_map tcl x ) )``,

reverse (
Induct_on `scl` >>
Induct_on `tcl` 
) >- (

rpt strip_tac >>
SIMP_TAC list_ss [find_topmost_map_def] >>
fs[INDEX_FIND_def] >>

Cases_on `(ALOOKUP h' x)` >>
Cases_on `(ALOOKUP h  x)` >>
fs[] >| [

 (* use IH *)
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`R`, `x`, `tcl`])) >>
  `similarl R tcl scl` by fs[similarl_def] >>
  gvs[] >>
  fs[find_topmost_map_def] >>
  Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) scl` >> fs[] >>
  Cases_on `INDEX_FIND 1 (λsc. IS_SOME (ALOOKUP sc x)) scl` >> fs[] >>
  Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc x)) tcl` >> fs[] >>
  Cases_on `INDEX_FIND 1 (λsc. IS_SOME (ALOOKUP sc x)) tcl` >> fs[] >>
  IMP_RES_TAC P_NONE_hold >> 
  IMP_RES_TAC P_NONE_hold2 >> gvs[]

 ,

   `similar R h h'` by fs[similarl_def] >>
   IMP_RES_TAC R_ALOOKUP_NONE_scopes >> gvs[]
 ,

   `similar R h h'` by fs[similarl_def] >>
   IMP_RES_TAC R_ALOOKUP_NONE_scopes >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`x`])) >> gvs[]
])>>
RW_TAC list_ss [similarl_def, similar_def] >>
EVAL_TAC
);







val R_implies_topmost_map_scopesl = prove (``
! R x l1 l2 scl tcl.
       ( similarl R tcl scl) ==>
       
       ((SOME l1 = topmost_map tcl x) ==>
(? l2 . SOME l2 = topmost_map scl x /\
        similar R l1 l2)) /\
((SOME l2 = topmost_map scl x) ==>
(? l1 . SOME l1 = topmost_map tcl x /\
        similar R l1 l2)) ``,	

reverse (Induct_on `tcl` >>
         Induct_on `scl` ) >-

(
rpt strip_tac >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`R`, `x`,`l1`, `l2`, `scl`])) >>

fs[topmost_map_def] >>
gvs[] >>

Cases_on `find_topmost_map (h'::tcl) x` >> gvs[] >>
Cases_on `find_topmost_map (h::scl) x` >> gvs[] >| [

IMP_RES_TAC R_ALOOKUP_NONE_scopelist >> gvs[]
,

PairCases_on `x'`>>
PairCases_on `x''`>>
gvs[] >>

IMP_RES_TAC R_find_topmost_map_scopesl >> gvs[] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`(x'0,l1)`])) >>
gvs[]
,
IMP_RES_TAC R_ALOOKUP_NONE_scopelist >> gvs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >>
gvs[]
,
PairCases_on `x'`>>
PairCases_on `x''`>>
gvs[] >>

IMP_RES_TAC R_find_topmost_map_scopesl >> gvs[] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`(x'0,x'1)`])) >>
gvs[]
]

) >>
fs[topmost_map_def, find_topmost_map_def, similar_def, similarl_def] >>
fs[INDEX_FIND_def]
);






val R_implies_lookup_map_scopesl = prove ( ``

! R v x t (scl :(varn # β) list list) (tcl :(varn # α) list list).
similarl R tcl scl ==> (
(SOME t = lookup_map tcl x ==>
(? v . SOME v = lookup_map scl x /\ (R t v))) /\
(SOME v = lookup_map scl x ==>
(? t . SOME t = lookup_map tcl x /\ (R t v)))
)``,

REPEAT STRIP_TAC >>
fs[lookup_map_def] >>

Cases_on `topmost_map tcl x` >>
Cases_on `topmost_map scl x` >> gvs[] >| [

IMP_RES_TAC R_implies_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`x'`])) >>
gvs[]
,

(* we need to show that x'' and x' have a relation between them*)
IMP_RES_TAC R_implies_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`x'`])) >>
gvs[] >>

(* then if we look up, it should also have a relation *)
Cases_on `ALOOKUP x' x` >>
Cases_on `ALOOKUP x'' x` >> gvs[] >| [

drule  R_ALOOKUP_NONE_scopes >>
strip_tac >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`t`,`x`])) >>
gvs[]
,
drule R_ALOOKUP_scopes >>
strip_tac >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x''''`, `x`, `t`])) >>
gvs[]
]


,
(* third subgoal *)

IMP_RES_TAC R_implies_topmost_map_scopesl >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`x'`])) >>
gvs[]

,



(* we need to show that x'' and x' have a relation between them*)
IMP_RES_TAC R_implies_topmost_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`x'`])) >>
gvs[] >>

(* then if we look up, it should also have a relation *)
Cases_on `ALOOKUP x' x` >>
Cases_on `ALOOKUP x'' x` >> gvs[] >| [

drule  R_ALOOKUP_NONE_scopes >>
strip_tac >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`t`,`x`])) >>
gvs[]
,
drule R_ALOOKUP_scopes >>
strip_tac >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`v`, `x`, `x'''`])) >>
gvs[]
]
]
);




val varn_tau_exists_in_scl_tscl = prove ( `` 
! gsl gtsl sl tsl varn v tau .
          type_scopes_list gsl gtsl ∧
          type_scopes_list sl tsl  ==>
	  
          ((SOME v = lookup_vexp2 sl gsl varn ==>
          ?tau. SOME tau = lookup_tau tsl gtsl varn /\
          v_typ v (t_tau_tau tau) F)   /\
          (SOME tau = lookup_tau tsl gtsl varn ==>
          ?v. SOME v = lookup_vexp2 sl gsl varn /\
          v_typ v (t_tau_tau tau) F)
	  ) ``,



gvs[lookup_tau_def] >>
fs[lookup_vexp2_def] >>
REPEAT STRIP_TAC >>
(subgoal `type_scopes_list (sl ⧺ gsl) (tsl ⧺ gtsl)` >-
IMP_RES_TAC type_scopes_list_APPEND) >>

Cases_on `lookup_map (sl ⧺ gsl) varn` >>
Cases_on `lookup_map (tsl ⧺ gtsl) varn` >>
fs[type_scopes_list_def] >> rw[] >| [

IMP_RES_TAC R_implies_lookup_map_scopesl >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`varn`, `x`])) >>
gvs[]
,

PairCases_on `x` >> gvs[] >>


drule R_lookup_map_scopesl >>
rpt strip_tac >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`x'`, `varn`, `(v,x1)`])) >>
gvs[] 


,
drule R_implies_lookup_map_scopesl >>
rpt strip_tac >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`tau`, `varn`, `v`])) >>
gvs[]
,

PairCases_on `x` >> gvs[] >>


drule R_lookup_map_scopesl >>
rpt strip_tac >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`tau`, `varn`, `(x0,x1)`])) >>
gvs[] 

]
);








val star_tau_exists_in_scl_tscl = prove ( ``

! gsl gtsl sl tsl v tau f.
star_not_in_sl (sl) /\
type_scopes_list gsl gtsl ==>

((SOME tau = find_star_in_globals gtsl (varn_star f) ==>
 ∃v. SOME v = lookup_vexp2 sl gsl (varn_star f)) /\
 (SOME v = lookup_vexp2 sl gsl (varn_star f) ==>
 ? tau . (SOME tau = find_star_in_globals gtsl (varn_star f)
 )))``,


gvs[lookup_tau_def] >>
fs[lookup_vexp2_def] >>
fs[find_star_in_globals_def] >>
rpt strip_tac >| [

 Cases_on `lookup_map gtsl (varn_star f)`>>
 Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >>
 gvs[] >| [

`lookup_map (sl)  (varn_star f) = NONE /\
 lookup_map (gsl) (varn_star f) = NONE` by (IMP_RES_TAC lookup_map_concat_none >> gvs[] ) >>
 fs[star_not_in_sl_def] >>
 gvs[type_scopes_list_def] >>
 drule R_implies_lookup_map_scopesl >>
 rpt strip_tac >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`tau`, `(varn_star f)`, `(x0,x1)`])) >>
 gvs[]

,

 PairCases_on `x'` >> gvs[]

]

,
(* sec *)


 Cases_on `lookup_map gtsl (varn_star f)`>>
 Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >>
 gvs[] >>
 PairCases_on `x` >> gvs[] >>
 IMP_RES_TAC lookup_map_in_gsl_lemma >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`v`, `x1`, `gsl`, `f`])) >> gvs[] >>



 gvs[type_scopes_list_def] >>
 drule R_implies_lookup_map_scopesl >>
 rpt strip_tac >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`v`, `(varn_star f)`, `(v,x1)`])) >>
 gvs[]
]
);



val P_hold_on_next = prove (``
  !i l P m.  (INDEX_FIND (SUC i) P l = SOME m) =
             (INDEX_FIND i P l = SOME (FST m - 1, SND m) /\ (0 < FST m))``, cheat);



val P_implies_next = prove (``
    !l P i m. INDEX_FIND 0 P l = SOME (i, m) ==>
              INDEX_FIND 1 P l = SOME (SUC i, m)
``, cheat);



val FIND_in_typl_imp_rec = prove ( ``
!l x0 tau s.
FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) l) = SOME (x0,tau) ==>
(∃v'. FIND (λ(k,v). k = s) (MAP (λ(x_,v_,tau_). (x_,v_)) l) = SOME (s,v') /\
s=x0
)``,

Induct_on `l` >>

fs[FIND_def] >>
fs[INDEX_FIND_def] >>

REPEAT STRIP_TAC >>
PairCases_on `z` >>
PairCases_on `h` >>
gvs[] >>

Cases_on `h0 = s` >>
gvs[] >>

   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#γ)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`0`,`(MAP (λ(x_,v_,tau_). (x_,tau_)) l)`,
    `(λ(xm,tm). xm = s)`, `(z0,x0,tau)`])) >>
   gvs[GSYM ADD1] >> 


 RES_TAC >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`,`tau`])) >>
 fs[] >>
 PairCases_on `z` >> gvs[] >>

 IMP_RES_TAC P_implies_next >>
 srw_tac [SatisfySimps.SATISFY_ss][]
);




val correct_field_type_FIND = prove ( ``
! s tau l  .
correct_field_type (MAP (λ(x_,v_,tau_). (x_,tau_)) l) s tau ==>
∃v'. FIND (λ(k,v). k = s) (MAP (λ(x_,v_,tau_). (x_,v_)) l) = SOME (s,v')``,


gvs[correct_field_type_def] >>
fs[tau_in_rec_def] >>
REPEAT STRIP_TAC >>

Cases_on `FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) l)` >> fs[] >>
PairCases_on `x` >> fs[] >>
Cases_on `x1 = tau`>> gvs[] >>
IMP_RES_TAC FIND_in_typl_imp_rec >>
 srw_tac [SatisfySimps.SATISFY_ss][]
);





val is_const_val_exsist = prove ( ``
! e . is_const e <=> (?v . e = e_v v) ``,
Cases_on `e` >>
fs[is_const_def]
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





(*
(*val oper =  ``binop_mul``;*)

fun bv_bv_prog (oper) = prove (``
! bitv bitv'.
bs_width bitv > 0 /\ bs_width bitv <= 64 /\
bs_width bitv = bs_width bitv' /\
is_bv_op(^oper) ==>
∃bitv''. bitv_binop (^oper) bitv bitv' = SOME bitv'' ``,

fs[is_bv_op_def] >>

Cases_on `bitv` >>
Cases_on `bitv'` >>

rpt strip_tac >>
gvs[bs_width_def] >>

IMP_RES_TAC bit_range >>
fs[] >>

fs[bitv_binop_def] >>
RW.ONCE_RW_TAC [bitv_binop_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][] 
);


val bv_bv_opl = map bv_bv_prog [ ``binop_mul``,  ``binop_add``,   ``binop_div``,   ``binop_mod``,
                            ``binop_sub``, ``binop_shl``, ``binop_shr``, `` binop_and``,
			    ``binop_or``, ``binop_xor`` ];

*)







val bv_bv_prog = prove (``
! bitv bitv' oper.
bs_width bitv > 0 /\ bs_width bitv <= 64 /\
bs_width bitv = bs_width bitv' /\
is_bv_op(oper) ==>
∃bitv''. bitv_binop (oper) bitv bitv' = SOME bitv'' ``,

fs[is_bv_op_def] >>

Cases_on `bitv` >>
Cases_on `bitv'` >>

rpt strip_tac >>
gvs[bs_width_def] >>

drule bit_range >>
rpt strip_tac >>
RES_TAC >>
gvs[NOT_CLAUSES] >>

fs[bitv_binop_def] >>
RW.ONCE_RW_TAC [bitv_binop_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][] 
);



(* TODO: fix this one as well theorm to make it fast, sol below *)
val bv_bv_bool_prog = prove (``
! bitv bitv' op.
bs_width bitv > 0 /\ bs_width bitv <= 64 /\
bs_width bitv = bs_width bitv' /\
is_bv_bool_op(op) ==>
∃b. bitv_binpred op bitv bitv' = SOME b ``,


fs[is_bv_bool_op_def] >>

Cases_on `bitv` >>
Cases_on `bitv'` >>

rpt strip_tac >>
gvs[bitv_binpred_def, bs_width_def] >>


rpt strip_tac >>
gvs[bs_width_def] >>

drule bit_range >>
rpt strip_tac >>
RES_TAC >>
gvs[NOT_CLAUSES] >>

fs[] >>
RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][]
);





val not_const_unred_mem = prove ( `` ! el .
¬is_consts el ==>
(? i . i <LENGTH el /\ unred_mem_index el = SOME i) ``,

REPEAT STRIP_TAC>>
FULL_SIMP_TAC std_ss [unred_mem_index_def] >>
Cases_on `unred_mem el` >>
fs[is_consts_def, unred_mem_def] >>

FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
IMP_RES_TAC not_index_none_exist >>

PairCases_on `x` >>
gvs[INDEX_FIND_EQ_SOME_0] 
);



val unred_mem_is_const = prove (``
!l i. i < LENGTH l /\ unred_mem_index l = SOME i  ==>
~is_const (EL i (l)) `` ,

REPEAT STRIP_TAC >>
fs[unred_mem_index_def] >>

Cases_on `unred_mem l` >> gvs[] >>
PairCases_on `x` >> gvs [] >>

gvs[unred_mem_def] >>
IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
gvs[]
);



val notlval_case = prove ( ``
!e . 
¬is_e_lval (e) ==>
(¬is_const (e) \/ (?v. e = e_v v)) ``,

Induct_on `e` >>
gvs[is_e_lval_def, is_const_def, get_lval_of_e_def] >>
gvs[]
)


val unred_arg_eq = prove ( ``! dl el .  
unred_arg_index dl el ≠ NONE <=>
? i . unred_arg_index dl el  = SOME i ``,	  

fs[unred_arg_index_def] >>
rpt strip_tac >>
Cases_on `find_unred_arg dl el` >>
gvs[] >>
PairCases_on `x` >> gvs[]
);




val correct_field_access = prove ( ``
! x_v_tau_list s tau' v boolv.
correct_field_type (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list) s tau' /\
(v = v_header boolv \/ v = v_struct )==>
∃v'. acc_f (v (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list)) s =
            SOME v' ``,

REPEAT STRIP_TAC >>
gvs[] >>
fs[acc_f_def] >>
CASE_TAC >>
IMP_RES_TAC correct_field_type_FIND >>
gvs[]
);




val e_T_get_lval = prove ( ``
! e gtsl tsl gscope scopest T_e tau .
 type_scopes_list gscope gtsl  /\
 type_scopes_list scopest tsl  /\
e_typ (gtsl,tsl) T_e e (tau) T ==>
? v . get_lval_of_e e = SOME (v) ``,

REPEAT STRIP_TAC >>
PairCases_on `T_e` >>
ASSUME_TAC e_lval_tlval >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `e`, `T`, `tsl`, `gtsl`, `T_e0`,`T_e1`,`T_e2`,`T_e3`,`T_e4`,`T_e5`,
	 ` tau`, `gscope`, `scopest`])) >>
gvs[] >>
fs[is_e_lval_def] >>
Cases_on `get_lval_of_e e` >> gvs[]
);








val is_get_lval = prove ( ``
!e . is_e_lval e <=> ? lval . get_lval_of_e e = SOME lval ``,
  fs[is_e_lval_def] >>
  STRIP_TAC >>
  Cases_on `get_lval_of_e e` >> gvs[]
 );






val INDEX_FIND_same_list_2 = prove ( ``
! l s i i' s' s'' v t .
INDEX_FIND 0 (λ(k,v). k = s) (MAP (λ(x,v,t). (x,v)) l) = SOME (i,s',v) /\
INDEX_FIND 0 (λ(xm,tm). xm = s) (MAP (λ(x,v,t). (x,t)) l) = SOME (i',s'',t) ==>
(i = i' /\ s = s'' /\ s = s /\ i < LENGTH l /\
v = EL i (MAP (λ(x,v,t). v) l) /\
t = EL i (MAP (λ(x,v,t). t) l)
 ) ``,

REPEAT GEN_TAC >>
STRIP_TAC >>

subgoal `   i' < LENGTH (MAP (λ(x,v,t). (x,t)) l) /\
    i < LENGTH (MAP (λ(x,v,t). (x,v)) l)  /\
     EL i' (MAP (λ(x,v,t). (x,t)) l) = (s'',t) /\
    EL i (MAP (λ(x,v,t). (x,v)) l) = (s',v) /\
     (λ(xm,tm). xm = s) (s'',t) /\
     (λ(k,v). k = s) (s',v)`  >- (IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]) >>
    
gvs[] >>

IMP_RES_TAC INDEX_FIND_same_list >> gvs[] >>
gvs[EL_simp5]
);




val FIND_same_list = prove (``
! l s s' s'' v t .
FIND (λ(k,v). k = s) (MAP (λ(x,v,t). (x,v)) l) =
        SOME (s',v) /\
FIND (λ(xm,tm). xm = s) (MAP (λ(x,v,t). (x,t)) l) =
        SOME (s'',t) ==>	
(s = s'' /\ s = s /\ 
(? i i' . i < LENGTH l  /\ i = i' /\
   v = EL i (MAP (λ(x,v,t). v) l) /\
   t = EL i (MAP (λ(x,v,t). t) l))) ``,

 REPEAT GEN_TAC >>
 STRIP_TAC >>
 fs[FIND_def] >>
 PairCases_on `z` >> PairCases_on `z'` >> gvs[] >>
 IMP_RES_TAC INDEX_FIND_same_list_2 >>
 gvs[] >>
  Q.EXISTS_TAC `z'0` >>
  gvs[]
);








val var_lval_is_typed = prove ( ``
! e v tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
e_typ (gtsl,tsl) T_e (e_var v) tau T ==>
        ∃lval v'.
          get_lval_of_e (e_var v) = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v' ∧ v_typ v' tau F ``,

rw[] >>
`∃v'. get_lval_of_e (e_var v) = SOME v'`  by (IMP_RES_TAC e_T_get_lval >> gvs[]) >>
gvs[] >>

Cases_on `v` >> 
fs[Once e_typ_cases] >>
gvs[]  >| [

(`? v'' . SOME v'' = lookup_vexp2 scopest gscope (varn_name s) ` by
(IMP_RES_TAC varn_tau_exists_in_scl_tscl >>  srw_tac [SatisfySimps.SATISFY_ss][])) >>

fs[get_lval_of_e_def] >>
fs[lookup_vexp2_def] >>
Cases_on `lookup_map (scopest ⧺ gscope) (varn_name s)` >> gvs[] >>

fs[lookup_lval_def, lookup_v_def] >>
PairCases_on `x` >> gvs[] >>

fs[lookup_tau_def] >>
Cases_on `lookup_map (tsl ⧺ gtsl) (varn_name s)` >> gvs[] >>

`type_scopes_list (scopest ⧺ gscope) (tsl ⧺ gtsl)` by
(IMP_RES_TAC type_scopes_list_APPEND) >>
ASSUME_TAC R_lookup_map_scopesl >>
gvs[type_scopes_list_def] >>


  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                         ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>
			 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(λx y. v_typ (FST x) (t_tau_tau y) F)`, `(tau')`, `(varn_name s)`,
  `(v'',x1)`, `(tsl ⧺ gtsl)`,`(scopest ⧺ gscope)`])) >> gvs[]
,


(`? v'' . SOME v'' = lookup_vexp2 scopest gscope (varn_star f) ` by
(IMP_RES_TAC star_tau_exists_in_scl_tscl >>  srw_tac [SatisfySimps.SATISFY_ss][])) >>



fs[get_lval_of_e_def] >>
fs[lookup_vexp2_def] >>
Cases_on `lookup_map (scopest ⧺ gscope) (varn_star f)` >> gvs[] >>


fs[lookup_lval_def, lookup_v_def] >>
PairCases_on `x` >> gvs[] >>


fs[find_star_in_globals_def] >>
Cases_on `lookup_map gtsl (varn_star f)` >> gvs[] >>

IMP_RES_TAC lookup_map_in_gsl_lemma >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`v''`, `x1`, `gscope`,
  `f`])) >> gvs[] >>


  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                         ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>

		 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(λx y. v_typ (FST x) (t_tau_tau y) F)`, `(tau')`, `(varn_star f)`,
  `(v'',x1)`, `(gtsl)`,`(gscope)`])) >> gvs[type_scopes_list_def]
]

);
















(* THIS?? out_dir_lookup_typed without wf_args *) 
(* TODO: move it to SR *)

val e_lval_WT = prove ( ``
! e x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
is_e_lval e /\
e_typ (gtsl,tsl) T_e e tau T ==>
        (∃lval v.
          get_lval_of_e e = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v /\
	  v_typ v tau F) ``,
	  

Induct >>
REPEAT STRIP_TAC >~ [`∃lval v.
          get_lval_of_e (e_acc e s) = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v ∧ v_typ v tau F`] >- (

fs[] >>

(subgoal `? v . get_lval_of_e (e_acc e s) = SOME v`
>- ( IMP_RES_TAC e_T_get_lval >> gvs[])  >>
gvs[]) >>

OPEN_EXP_TYP_TAC ``(e_acc e s)`` >> fs[] >>
Cases_on `struct_ty` >> gvs[] >>

(subgoal `? v . get_lval_of_e (e) = SOME v`
>- ( IMP_RES_TAC e_T_get_lval >> gvs[])  >>
gvs[clause_name_def]) >>

fs [is_get_lval] >| [

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(t_tau_tau (tau_xtl struct_ty_struct x_tau_list))`,
	 `gtsl`, `gscope`,`tsl`,`scopest`,`T_e`])) >> gvs[] >>

Q.PAT_X_ASSUM `get_lval_of_e (e_acc e s) = SOME v`
( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [get_lval_of_e_def] ) >>
gvs[] >>

 OPEN_V_TYP_TAC ``v''`` >> fs[] >>
 gvs[] >>

 (*IMP_RES_TAC  correct_field_access*)
 IMP_RES_TAC correct_field_type_FIND >>
  fs[lookup_lval_def] >>
 fs[acc_f_def] >>
 fs[correct_field_type_def] >>
 fs[tau_in_rec_def] >>
 Cases_on `FIND (λ(xm,tm). xm = s)
             (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` >> gvs[] >>

 PairCases_on `x` >> gvs[] >>
 Cases_on `x1 = tau'` >> gvs[] >>
 IMP_RES_TAC FIND_same_list >>
 gvs[]

,



FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(t_tau_tau (tau_xtl struct_ty_header x_tau_list))`,
	 `gtsl`, `gscope`,`tsl`,`scopest`,`T_e`])) >> gvs[] >>

Q.PAT_X_ASSUM `get_lval_of_e (e_acc e s) = SOME v`
( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [get_lval_of_e_def] ) >>
gvs[] >>

 OPEN_V_TYP_TAC ``v''`` >> fs[] >>
 gvs[] >>

 (*IMP_RES_TAC  correct_field_access*)
 IMP_RES_TAC correct_field_type_FIND >>
  fs[lookup_lval_def] >>
 fs[acc_f_def] >>
 fs[correct_field_type_def] >>
 fs[tau_in_rec_def] >>
 Cases_on `FIND (λ(xm,tm). xm = s)
             (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` >> gvs[] >>

 PairCases_on `x` >> gvs[] >>
 Cases_on `x1 = tau'` >> gvs[] >>
 IMP_RES_TAC FIND_same_list >>
 gvs[]
]

) >~ [`∃lval v.
          get_lval_of_e (e_slice e e' e'') = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v ∧ v_typ v tau F`] >- (


 OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >> fs[] >>
 `(? v''' . get_lval_of_e (e) = SOME v''')` by  (IMP_RES_TAC e_T_get_lval >> gvs[]) >>

 gvs[is_get_lval, get_lval_of_e_def] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(t_tau_tau (tau_bit w))`,
  `gtsl`,
  `gscope`,
  `tsl`,
  `scopest`,
 `T_e`])) >>
 gvs[] >>

 fs[Once v_typ_cases] >>
 SIMP_TAC list_ss [lookup_lval_def] >> gvs[] >>
 PairCases_on `bitv''` >>
 gvs[] >>

 fs[slice_lval_def] >>
 PairCases_on `bitv` >> PairCases_on `bitv'` >>
 gvs[] >>

 gvs[slice_def, bs_width_def, bitv_bitslice_def, vec_to_const_def]
) >~ [` ∃lval v'.
          get_lval_of_e (e_var v) = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v' ∧ v_typ v' tau F `] >- (

IMP_RES_TAC var_lval_is_typed >> gvs[]
) >>
fs[get_lval_of_e_def] >>
fs[Once e_typ_cases] >>
fs[Once v_typ_cases]

);
















(* TO DO : move to the SR and make sure to add it to the CI*)

val wf_arg_single_implied  =  prove ( ``
! e d b x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
out_is_lval [d] [b] /\
is_arg_red d e /\
e_typ (gtsl,tsl) T_e  (e) (tau) (b) ==>
wf_arg d x e (scopest ⧺ gscope) ``,

rw[] >>
rpt strip_tac >>
Cases_on `is_d_out d` >>
fs[is_arg_red_def] >>
fs[wf_arg_def] >| [
fs[out_is_lval_def] >>

  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`0`])) >>
  gvs[] >>
IMP_RES_TAC e_lval_WT >> gvs[]
,

gvs[is_const_val_exsist] >>
fs[v_of_e_def]
]);




val wf_arg_single_implied_2  =  prove ( ``
! e d b x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
is_d_out d ⇒ b /\
is_arg_red d e /\
e_typ (gtsl,tsl) T_e  (e) (tau) (b) ==>
wf_arg d x e (scopest ⧺ gscope) ``,

rw[] >>
rpt strip_tac >>
Cases_on `is_d_out d` >>
fs[is_arg_red_def] >>
fs[wf_arg_def] >>
IMP_RES_TAC e_lval_WT >> gvs[]
);




(****************************************************************************)



(* TO DO : move to SR proof and simplify the goal *)
val wf_arg_normalization_new = prove (``
! d dl x xl e el ss.
wf_arg_list (d::dl) (x::xl) (e::el) ss <=>
wf_arg d x e ss /\ wf_arg_list (dl) (xl) (el) ss ``,

REPEAT STRIP_TAC >>
fs[wf_arg_list_def] >>
EQ_TAC >>
REPEAT STRIP_TAC >|[

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`0`])) >>
 fs[wf_arg_def] 
 ,
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i+1`])) >>
 gvs[] >>
 fs[EL_CONS] >>
 fs[PRE_SUB1]
 ,
 fs[Once EL_compute] >>
 CASE_TAC >>
 gvs[EL_CONS] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i-1`])) >>

 gvs[] >>
 Cases_on `i ≤ 1` >| [
 
  `i=1` by fs[] >> rw[] >>
  rfs[]
 ,
  fs[PRE_SUB1] >>

  rfs[GSYM EL] >>
  gvs[ADD1]
]]
);




(*TODO: same proof as above, should be addded together *)
val out_is_lval_normalisation = prove ( ``
! dl bl d b .
out_is_lval (d::dl) (b::bl) <=>
(out_is_lval (dl) (bl) /\ (is_d_out (d) ⇒ b)) ``,

gvs[out_is_lval_def] >>
REPEAT STRIP_TAC >>
EQ_TAC >>
REPEAT STRIP_TAC >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i+1`])) >>
 gvs[] >>
 fs[EL_CONS] >>
 fs[PRE_SUB1]
 ,
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`0`])) >>
 fs[] 
 ,
 

 fs[Once EL_compute] >>
 CASE_TAC >>
 gvs[EL_CONS] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`i-1`])) >>

 gvs[] >>
 Cases_on `i ≤ 1` >| [
 
  `i=1` by fs[] >> rw[] >>
  rfs[]
 ,
  fs[PRE_SUB1] >>

  rfs[GSYM EL] >>
  gvs[ADD1]
]
]);





val check_args_red_normalize2_new = prove (``
! dl el  d e . 
check_args_red (d::dl) (e::el) <=>
(check_args_red dl el /\
check_args_red [d] [e] ) ``,

fs[check_args_red_def] >>
srw_tac [boolSimps.DNF_ss][] >>
EQ_TAC >> gvs[]
);






	






val wf_arg_full_implied  =  prove ( ``
! e_tau_d_b_t_list gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
out_is_lval (MAP (λ(e_,tau_,d_,b_,x_). d_) e_tau_d_b_t_list)
            (MAP (λ(e_,tau_,d_,b_,x_). b_) e_tau_d_b_t_list) /\
check_args_red (MAP (λ(e_,tau_,d_,b_,x_). d_) e_tau_d_b_t_list)
               (MAP (λ(e_,tau_,d_,b_,x_). e_) e_tau_d_b_t_list) /\
     (! i . i < LENGTH e_tau_d_b_t_list ⇒
            e_typ (gtsl,tsl)
              (T_e)
              (EL i (MAP (λ(e_,tau_,d_,b_,x_). e_) e_tau_d_b_t_list))
              (t_tau_tau (EL i (MAP (λ(e_,tau_,d_,b_,x_). tau_) e_tau_d_b_t_list)))
              (EL i (MAP (λ(e_,tau_,d_,b_,x_). b_) e_tau_d_b_t_list))) ==>
wf_arg_list (MAP (λ(e_,tau_,d_,b_,x_). d_) e_tau_d_b_t_list)
 	      (MAP (λ(e_,tau_,d_,b_,x_). x_) e_tau_d_b_t_list)
              (MAP (λ(e_,tau_,d_,b_,x_). e_) e_tau_d_b_t_list)
	      (scopest++gscope) ``,


Induct >>
REPEAT STRIP_TAC >>
gvs[] >-
fs[wf_arg_list_def] >>
PairCases_on `h` >> gvs[] >>

gvs[wf_arg_normalization_new] >>
gvs[out_is_lval_normalisation] >>
gvs[Once check_args_red_normalize2_new] >>

CONJ_TAC >| [

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`0`])) >>
 gvs[] >>

ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:string``  ] wf_arg_single_implied_2) >>


 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`h0`, `h2`, `h3`, `h4`, `(t_tau_tau h1)`, `gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>

 gvs[] >>
 
gvs[check_args_red_def] >>

Cases_on `is_d_out h2` >> gvs[] >>

fs[is_arg_red_def] >>
gvs[is_const_val_exsist] >>

fs[wf_arg_def] >>
fs[v_of_e_def] 

,



subgoal `(∀i. i < LENGTH e_tau_d_b_t_list ⇒
               e_typ (gtsl,tsl) T_e
                 (EL i (MAP (λ(e_,tau_,d_,b_,x_). e_) e_tau_d_b_t_list))
                 (t_tau_tau
                    (EL i (MAP (λ(e_,tau_,d_,b_,x_). tau_) e_tau_d_b_t_list)))
                 (EL i (MAP (λ(e_,tau_,d_,b_,x_). b_) e_tau_d_b_t_list)))` >-
( REPEAT STRIP_TAC >>

  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`i + 1` ])) >>
  gvs[ADD1] >>
  fs[EL_CONS] >>
  fs[PRE_SUB1] ) >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[]
]
);









val map_distrub_penta = prove ( ``
! l1 l2 l3 l4 l5.
(LENGTH l1 = LENGTH l2 /\
LENGTH l2 = LENGTH l3 /\
LENGTH l3 = LENGTH l4 /\
LENGTH l4 = LENGTH l5) ==>
((MAP (λ(e_,t_,d_,b_,x_). e_) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l1 /\
 (MAP (λ(e_,t_,d_,b_,x_). t_) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l2 /\
 (MAP (λ(e_,t_,d_,b_,x_). d_) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l3 /\
 (MAP (λ(e_,t_,d_,b_,x_). b_) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l4 /\
 (MAP (λ(e_,t_,d_,b_,x_). x_) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l5
) ``,

Induct_on `l1` >>
Induct_on `l2` >>
Induct_on `l3` >>
Induct_on `l4` >>
Induct_on `l5` >>

REPEAT STRIP_TAC >>
gvs[]
);





val wf_arg_full_implied_2  =  prove ( ``
! xl bl el dl tl gtsl gscope tsl scopest T_e .
LENGTH bl = LENGTH el /\
LENGTH el = LENGTH xl /\
LENGTH xl = LENGTH dl /\
LENGTH dl = LENGTH tl /\
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
out_is_lval dl bl /\
check_args_red dl el  /\
     (! i . i < LENGTH el ⇒
            e_typ (gtsl,tsl)
              (T_e)
              (EL i el)
              (t_tau_tau (EL i tl))
              (EL i bl)) ==>
wf_arg_list dl xl el (scopest++gscope) ``,

REPEAT STRIP_TAC >>
ASSUME_TAC wf_arg_full_implied >>


 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`ZIP (el,ZIP(tl,ZIP(dl,ZIP (bl,xl))))`, `gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[] >>


  `(MAP (λ(e_,tau_,d_,b_,x_). e_)
             (ZIP (el,ZIP (tl,ZIP (dl,ZIP (bl,xl)))))) = el` by gvs[GSYM map_distrub_penta] >>


  `(MAP (λ(e_,tau_,d_,b_,x_). tau_)
             (ZIP (el,ZIP (tl,ZIP (dl,ZIP (bl,xl)))))) = tl` by gvs[GSYM map_distrub_penta] >>

  `(MAP (λ(e_,tau_,d_,b_,x_). d_)
             (ZIP (el,ZIP (tl,ZIP (dl,ZIP (bl,xl)))))) = dl` by gvs[GSYM map_distrub_penta] >>

  `(MAP (λ(e_,tau_,d_,b_,x_). b_)
             (ZIP (el,ZIP (tl,ZIP (dl,ZIP (bl,xl)))))) = bl` by gvs[GSYM map_distrub_penta] >>

  `(MAP (λ(e_,tau_,d_,b_,x_). x_)
             (ZIP (el,ZIP (tl,ZIP (dl,ZIP (bl,xl)))))) = xl` by gvs[GSYM map_distrub_penta] >>


gvs[]

);




val wf_imp_ci_abstract_single = prove ( ``
! e d x ss  . 
wf_arg d x e (ss) ==>
? scope . copyin_abstract [x] [d] [e] (ss) scope``,

REPEAT STRIP_TAC  >>
Q.EXISTS_TAC `[(varn_name x ,
               THE (one_arg_val_for_newscope (d) (e) ss))]` >>


fs[copyin_abstract_def] >>
NTAC 2 STRIP_TAC >>
`i=0 /\ 0 <1` by fs[] >>
rw[] >>

IMP_RES_TAC wf_imp_val_lval >>
gvs[]
);






val wf_imp_new_vlval_list = prove ( ``
! i dl xl el ss.
(LENGTH xl = LENGTH dl) /\
(LENGTH dl = LENGTH el) /\
(i < LENGTH dl ) /\
wf_arg_list (dl) (xl) (el) ss ==>
? vlval . one_arg_val_for_newscope (EL i (dl)) (EL i (el)) ss = SOME vlval``,

Induct_on `xl` >>
Induct_on `dl` >>
Induct_on `el` >>
fs[] >>

REPEAT STRIP_TAC >>
fs[Once EL_compute] >>
CASE_TAC >>
gvs[] >| [

IMP_RES_TAC wf_arg_normalization >> 
IMP_RES_TAC wf_imp_val_lval >>
 srw_tac [SatisfySimps.SATISFY_ss][] 

,

IMP_RES_TAC wf_arg_normalization >> 

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`i-1`, `dl`, `el`, `ss`   ])) >>
   gvs[] >>

 Cases_on `i ≤ 1` >| [
 gvs[] >>
 `i=1` by fs[] >> rw[] >>
  gvs[EL]
 ,
 gvs[] >>
  `i>1` by fs[] >> rw[] >>

   gvs[GSYM EL_compute] >>
  fs[EL_CONS] >>
  fs[PRE_SUB1] >>

  rfs[GSYM EL] >>
  gvs[ADD1]
] ] );



val wf_arg_list_NONE2 = prove (``
! dl xl el ss .
(LENGTH xl = LENGTH dl) /\
(LENGTH dl = LENGTH el) /\
wf_arg_list dl xl el ss /\
ALL_DISTINCT xl ==>
~ (all_arg_update_for_newscope xl dl el  ss = NONE)``,

REPEAT STRIP_TAC >>
fs[all_arg_update_for_newscope_def] >>
ASSUME_TAC wf_arg_list_NONE >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`ZIP (dl,ZIP (xl,el))`])) >> gvs[] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`ss`])) >> gvs[] >| [

`(MAP (λ(d,x,e). x) (ZIP (dl,ZIP (xl,el)))) = xl` by gvs[GSYM map_distrub] >>
`~ ALL_DISTINCT xl` by fs[]
,

`(MAP (λ(d,x,e). x) (ZIP (dl,ZIP (xl,el)))) = xl` by gvs[GSYM map_distrub] >>
`(MAP (λ(d,x,e). e) (ZIP (dl,ZIP (xl,el)))) = el` by gvs[GSYM map_distrub] >>
`(MAP (λ(d,x,e). d) (ZIP (dl,ZIP (xl,el)))) = dl` by gvs[GSYM map_distrub] >>
`wf_arg_list (MAP (λ(d,x,e). d) (ZIP (dl,ZIP (xl,el))))
          (MAP (λ(d,x,e). x) (ZIP (dl,ZIP (xl,el))))
          (MAP (λ(d,x,e). e) (ZIP (dl,ZIP (xl,el)))) ss` by fs[]
]
);



(* TODO: put all the maps together and call them map simps file *)
val MAP_snd_quad_12_1 = prove ( `` !l .
  MAP SND (MAP (λ(e_,t_,d_,b_). (t_,d_)) l) =
          (MAP (λ(e_,t_,d_,b_). d_) l) ``,
Induct >>
REPEAT STRIP_TAC >>
gvs[] >>
PairCases_on `h` >>
gvs[]
);






val copyin_eq_rw = prove ( ``
! xl dl el gscope scopest scope.
   (LENGTH xl = LENGTH dl) /\
   (LENGTH dl = LENGTH el) /\     
     (ALL_DISTINCT xl) ∧
     (wf_arg_list dl xl el  (scopest ⧺ gscope))  ==>
( (SOME scope = copyin xl dl el gscope scopest)
<=>
copyin_abstract xl dl el (scopest ⧺ gscope) scope)
``,

REPEAT STRIP_TAC >>
ASSUME_TAC copyin_eq >>


FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`ZIP (el,ZIP (xl,dl))`, `gscope`, `scopest`, `scope`])) >> gvs[] >>
gvs[] >>

`(MAP (λ(e,x,d). x) (ZIP (el,ZIP (xl,dl)))) = xl` by gvs[GSYM map_distrub] >>
`(MAP (λ(e,x,d). d) (ZIP (el,ZIP (xl,dl)))) = dl` by gvs[GSYM map_distrub] >>
`(MAP (λ(e,x,d). e) (ZIP (el,ZIP (xl,dl)))) = el` by gvs[GSYM map_distrub] >>

gvs[]
);













val lookup_funn_t_map_NONE = prove (``
! delta_g delta_b delta_x func_map b_func_map ext_map f .
dom_tmap_neq delta_g delta_b /\
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
 REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
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
   
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[])

,
 
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >>
 gvs[]) 
 
,
 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`]))>>
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








(* DONE *)
val tfunn_imp_sig_body_lookup = prove ( ``
! apply_table_f ext_map func_map b_func_map pars_map tbl_map
  order t_scope_list_g delta_g delta_b delta_x tdl tau f.
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
       order t_scope_list_g delta_g delta_b delta_x /\
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x
 ==>
(? stmt xdl. SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map /\
  (MAP SND tdl = MAP SND xdl ) /\
  (LENGTH (MAP SND xdl) = LENGTH (MAP SND tdl) /\
   (ALL_DISTINCT (MAP FST xdl)))
) ``,

fs[WT_c_cases] >>
REPEAT STRIP_TAC >>

Cases_on `f` >| [


 (* functions global and block *)
 

 Cases_on `lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map` >> gvs[] >| [
      (* show that this is impossible *)
  ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a`` ] lookup_funn_t_map_NONE) >> 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`delta_g`, `delta_b`, ` delta_x`, ` func_map`, ` b_func_map`, ` ext_map`, `funn_name s`])) >> gvs[] 
    ,

    PairCases_on `x` >>
    ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a`` ] lookup_glb_local_ctx) >> 
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`func_map`, `delta_g`, ` func_map`, ` delta_b`, ` b_func_map`, ` s`, `x0`,
      ` x1`, ` tdl`,
      `ext_map`, ` delta_x`, `tau`])) >> gvs[] >> 

    fs[WTFg_cases, WTFb_cases] >>
    fs[func_map_typed_def, func_map_blk_typed_def] >>
    rfs[] >>
    RES_TAC >>

   Q.PAT_X_ASSUM `∀tdl. MAP SND tdl = MAP SND x1`
   ( STRIP_ASSUME_TAC o (Q.SPECL [
   `tdl` ])) >>
   `LENGTH (MAP SND tdl) = LENGTH (MAP SND x1)` by METIS_TAC [] >>
   gvs[]


    ]

,

(* func inst *)


 Cases_on `lookup_funn_sig_body (funn_inst s) func_map b_func_map ext_map` >> gvs[] >| [

 ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a`` ] lookup_funn_t_map_NONE) >> 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`delta_g`, `delta_b`, ` delta_x`, ` func_map`, ` b_func_map`, ` ext_map`, `funn_inst s`])) >> gvs[] 
 ,

 fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
 fs[t_lookup_funn_def] >>
 rfs[] >> rw[] >>

 Cases_on `ALOOKUP ext_map s` >>
 Cases_on `ALOOKUP delta_x s` >>
 fs[] >> rw[] >>

 PairCases_on `x` >> PairCases_on `x'` >> PairCases_on `x''` >> gvs[] >>
 Cases_on `x'0` >> Cases_on `x''0` >> gvs[] >>
 Cases_on `x` >> Cases_on `x'` >> gvs[] >>

 fs[WTX_cases] >>
 fs[extern_map_IoE_typed_def] >>

 RES_TAC >>
 gvs[] >>

   Q.PAT_X_ASSUM `∀tdl. MAP SND tdl = MAP SND q`
   ( STRIP_ASSUME_TAC o (Q.SPECL [
   `q'` ])) >>
   `LENGTH (MAP SND q') = LENGTH (MAP SND q)` by METIS_TAC [] >>
   gvs[]
]
,



 Cases_on `lookup_funn_sig_body ((funn_ext s s0)) func_map b_func_map ext_map` >> gvs[] >| [
  ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a`` ] lookup_funn_t_map_NONE) >> 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`delta_g`, `delta_b`, ` delta_x`, ` func_map`, ` b_func_map`, ` ext_map`, `funn_ext s s0`])) >> gvs[] 

 ,


 fs[lookup_funn_sig_def, lookup_funn_sig_body_def] >>
 fs[t_lookup_funn_def] >>
 rfs[] >> rw[]  >>

 Cases_on `ALOOKUP ext_map s` >>
 Cases_on `ALOOKUP delta_x s` >>
 fs[] >> rw[] >>

 PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
  PairCases_on `x''`  >> gvs[] >>
  
 Cases_on `ALOOKUP x''1 s0` >>
 Cases_on `ALOOKUP x'1 s0` >> gvs[] >>
 
 Cases_on `x` >> Cases_on `x'`  >> gvs[] >>

 fs[WTX_cases] >>
 fs[extern_MoE_typed_def] >>

 RES_TAC >>
 gvs[] >>
 
   Q.PAT_X_ASSUM `∀tdl. MAP SND tdl = MAP SND q'`
   ( STRIP_ASSUME_TAC o (Q.SPECL [
   `q` ])) >>
   `LENGTH (MAP SND q') = LENGTH (MAP SND q)` by METIS_TAC [] >>
   gvs[]
]

]
);






val tfunn_imp_sig_lookup = prove ( ``

! apply_table_f ext_map func_map b_func_map pars_map tbl_map
  order t_scope_list_g delta_g delta_b delta_x tdl tau f.
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) order t_scope_list_g delta_g delta_b delta_x /\
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x ==>
(? xdl . SOME (xdl) = lookup_funn_sig f func_map b_func_map ext_map  /\
              MAP SND tdl = MAP SND xdl ∧
         LENGTH (MAP SND xdl) = LENGTH (MAP SND tdl)  /\
	    (ALL_DISTINCT (MAP FST xdl))) ``,

REPEAT STRIP_TAC >>
fs[lookup_funn_sig_def] >>
Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >> fs[] >| [

  ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:'a`` ] lookup_funn_t_map_NONE) >> 
  fs[WT_c_cases] >> gvs[] >> RES_TAC >>
  srw_tac [] [] >>
  Cases_on `t_lookup_funn f delta_g delta_b delta_x ` >> fs[]

,

PairCases_on `x` >>
gvs[] >>

IMP_RES_TAC tfunn_imp_sig_body_lookup >>
gvs[]
]
);











val PROG_e =
prove (`` ! (ty:'a itself) .
(!e. prog_exp e ty) /\
(! (l1: e list). prog_exp_list l1 ty) /\
(! (l2: (string#e) list) .  prog_strexp_list l2 ty) /\
(! tup. prog_strexp_tup tup ty)   ``,

STRIP_TAC >>
Induct >| [

(*****************)
(*    values     *)
(*****************)

fs[prog_exp_def, is_const_def]

,

(*****************)
(*   variables   *)
(*****************)

fs[prog_exp_def] >>
rpt strip_tac >>
SIMP_TAC list_ss [Once e_red_cases] >>
gvs[] >>

(*now we need to show that there is indeed a value that we can find in
   the scopes *)
fs[Once e_typ_cases, clause_name_def] >| [

IMP_RES_TAC varn_tau_exists_in_scl_tscl >>
srw_tac [SatisfySimps.SATISFY_ss][]

,

IMP_RES_TAC star_tau_exists_in_scl_tscl >>
srw_tac [SatisfySimps.SATISFY_ss][]
]
,

(*****************)
(*   list of e   *)
(*****************)

fs[prog_exp_def] >>
fs[Once e_red_cases] >>
FULL_SIMP_TAC (srw_ss()) [Once e_typ_cases]

,


(*****************)
(* field access  *)
(*****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [
  gvs[] >>

  (* we know that the only constants can be used to be accessed
   are either a struct or a header *)
  Cases_on `e` >>
  fs[is_const_def] >>

  (*from the typing rules we know *)
  OPEN_EXP_TYP_TAC ``(e_v v)`` >> fs[] >>
  OPEN_V_TYP_TAC ``v`` >> fs[] >| [
  
(*access a struct *)

  gvs[lemma_v_red_forall, clause_name_def] >>
   RES_TAC >>
   IMP_RES_TAC correct_field_type_FIND >>
   srw_tac [SatisfySimps.SATISFY_ss][] 



,
(* access a header*)

  gvs[lemma_v_red_forall, clause_name_def] >>
   RES_TAC >>
   IMP_RES_TAC correct_field_type_FIND >>
   srw_tac [SatisfySimps.SATISFY_ss][] 

]
  ,

  (* nested expressions cases*)

  fs[prog_exp_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau (tau_xtl struct_ty x_tau_list)`, ` b`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,

(*****************)
(*  unary oper   *)
(*****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>
RW_TAC (srw_ss()) [Once e_red_cases] >>

rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [

Cases_on `u` >>
OPEN_EXP_TYP_TAC ``(e_unop u e)`` >>
fs[clause_name_def] >>
gvs[is_const_val_exsist] >>

(* for all cases *)

  gvs[lemma_v_red_forall] >>
  OPEN_EXP_TYP_TAC ``(e_v v)`` >> fs[] >>
  OPEN_V_TYP_TAC ``v`` >>
    srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]

,
(* expression part *)

OPEN_EXP_TYP_TAC ``(e_unop u e)`` >>

  fs[prog_exp_def] >>
 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `tau`, ` b'`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>

  gvs[] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]

]




,

(****************)
(*  binop       *)
(****************)  


simp_tac list_ss [prog_exp_def] >>
rpt strip_tac >>

(* start the proof by checking the typing rule, this will ease the work of the cases *)

OPEN_EXP_TYP_TAC ``(e_binop e b e')`` >>

(* obviously we should get 4  cases *)

rw_tac (srw_ss()) [] >| [

 (* first we need to show that we can progress from an binop expression
 typed as following:
 e : ( bs w , b )  binop  e'  : ( bs w , b' )  
 where binop is is_bv_op (takes two bs and returns the type bs ).
 NOTE: here all cases on the binop should be solved the same exact way.
      we should get 10 cases.
 *)

 Cases_on `b` >>
 fs[is_bv_op_def] >>

 (* now we can look into the reductions in the
   conclusion and start showing progress for each reduction case*)

 (
 RW_TAC (srw_ss()) [Once e_red_cases] >>
 rw[] >>
 srw_tac [boolSimps.DNF_ss][] >>


(* now we construct three cases on teh reduction rule,
   via checked teh cases on e being a constant
   e + e'
   v + e'
   v + v
*)


 Cases_on `is_const e` >| [
   Cases_on `is_const e'` >| [ 

   (* v + v *)
   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
  
   fs[] >>
   srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>
   (*gvs opli*)
   ASSUME_TAC bv_bv_prog >>
   gvs[is_bv_op_def]
   ,

   (* v + e' *)
   (* use IH for e', and use the typing rule for v *)

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  
    OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
    OPEN_V_TYP_TAC ``v`` >>
  
    fs[] >>
    srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>

   (* now show that e actually reduces from IH*) 
    fs[prog_exp_def] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit (bs_width (bitv : bool list # num))))`, ` b'''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]   
   ]
,
(* e + e' *)

 (* just show the e reduces *)
 fs[clause_name_def] >>
    gvs[is_const_val_exsist] >>
    gvs[lemma_v_red_forall, is_short_circuitable_def] >>

    fs[prog_exp_def] >>

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau (tau_bit w)`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>


  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   
]
)


,


(* second we need to show that we can progress from an binop expression typed as following
 e : ( bool , b )  binop  e'  : ( bool , b' )  
where binop is is_bool_op (takes two bool and returns the type bool )
*)

Cases_on `b` >>
fs[is_bool_op_def] >>


(


 RW_TAC (srw_ss()) [Once e_red_cases] >>
 rw[] >>
 srw_tac [boolSimps.DNF_ss][] >>

(* now we construct 5 cases on the reduction rule,
   via checked teh cases on e being a constant
   e op e'
   v op e'
   v op v' where v and v' typed as is either (bs, bool, or err)
*)


 Cases_on `is_const e` >| [
   Cases_on `is_const e'` >| [
    (* v op v' *)

   
   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>



   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v'`` >>
  
   fs[] 
   (*TODO:incorrect, v_ree is never typed in the bool op*)
,
    (* v op e' *)


   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  

   (* now show that e actually reduces from IH*) 
    fs[prog_exp_def] >>
  

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau (tau_bool)`, ` b'''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>


   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]  >>

   
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   gvs[]


]
,
    (* e op e' *)



 (* just show the e reduces *)
   fs[clause_name_def] >>
    gvs[is_const_val_exsist] >>
    gvs[lemma_v_red_forall, is_short_circuitable_def] >>

    fs[prog_exp_def] >>
    

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau (tau_bool)`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   
  ]

) 

,

(* third, we need to show that we can progress from an binop expression typed as following
 e : ( err , b )  binop  e'  : ( err , b' )  
where binop is is_err_bool (takes two err and returns the type bool )
*)



Cases_on `b` >>
fs[is_err_bool_def] >>

(
 RW_TAC (srw_ss()) [Once e_red_cases] >>
 rw[] >>
 srw_tac [boolSimps.DNF_ss][] >>

 
 Cases_on `is_const e` >| [
   Cases_on `is_const e'` >| [
    (* v op v' *)

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>

   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v'`` >>  
   fs[]


     ,
    (*v op e'*)

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  

   (* now show that e actually reduces from IH*) 

  fs[prog_exp_def] >>
  
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau tau_err`, ` b'''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>


   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]

  ]
  ,
   (* e op e' *)

  fs[clause_name_def] >>
    gvs[is_const_val_exsist] >>
    gvs[lemma_v_red_forall, is_short_circuitable_def] >>

    fs[prog_exp_def] >>
    

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau (tau_err)`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   

 ]

)


,

(* fourth, we need to show that we can progress from an binop expression typed as following
 e : ( bs w , b )  binop  e'  : ( bs w , b' )  
where binop is is_bool_op (takes two bs and returns the type bool )
*)




Cases_on `b` >>
fs[is_bv_bool_op_def] >>

(


 RW_TAC (srw_ss()) [Once e_red_cases] >>
 rw[] >>
 srw_tac [boolSimps.DNF_ss][] >> 

 
 Cases_on `is_const e` >| [
   Cases_on `is_const e'` >| [


   (* v + v *)
   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>



   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v'`` >>
  
   fs[] >>

   srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>
   ASSUME_TAC bv_bv_bool_prog >>
   gvs[is_bv_bool_op_def]


  ,




   (* v + e' *)
   (* use IH for e', and use the typing rule for v *)

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  

   (* now show that e actually reduces from IH*) 
    fs[prog_exp_def] >>
 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit w))`, ` b'''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]   


  
 
] ,




 (* just show the e reduces *)
 fs[clause_name_def] >>
    gvs[is_const_val_exsist] >>
    gvs[lemma_v_red_forall, is_short_circuitable_def] >>

    fs[prog_exp_def] >>
    
  
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit w))`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
	    
  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   
 ]
)

]



,

(****************)
(*  concat      *)
(****************)


SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [
 Cases_on `is_const e'` >| [

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall] >>
  
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>

   srw_tac [SatisfySimps.SATISFY_ss][]
,



   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall] >>
  
    OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
    OPEN_V_TYP_TAC ``v`` >>
  
    fs[] >>
    srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>

   (* now show that e actually reduces from IH*) 
    fs[prog_exp_def] >>

  
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit w2'))`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>


   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]   
  

] ,

  (* nested expressions cases*)

  fs[prog_exp_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit w1))`, ` b'`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,


(****************)
(*   slice      *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall] >>
  
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
      srw_tac [SatisfySimps.SATISFY_ss][]   


,


  fs[clause_name_def] >>
    gvs[is_const_val_exsist] >>
    gvs[lemma_v_red_forall] >>

    fs[prog_exp_def] >>
    
     LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `(t_tau_tau (tau_bit w))`, ` b`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   



]

,


(****************)
(*  call        *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_call f l1)`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>


PairCases_on `c` >> 
gvs[is_const_def, clause_name_def] >>


(* the cases should be on if there is an element unreduced yet? *)
Cases_on ` (unred_arg_index (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)
                 (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list) = NONE) ` >| [

DISJ1_TAC >>


IMP_RES_TAC unred_arg_index_NONE >>

 ASSUME_TAC tfunn_imp_sig_body_lookup >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, `order`, `t_scope_list_g`,
   `delta_g`, `delta_b`, `delta_x`,
   `(MAP (λ(e_,tau_,d_,b_).(tau_,d_)) (e_tau_d_b_list : (e # tau # d # bool) list))`,
   `tau'`, `f`])) >> gvs[] >>



Q.EXISTS_TAC `ZIP (
(MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list)
, ZIP(MAP FST xdl,MAP SND xdl))` >>

Q.EXISTS_TAC `stmt` >>


rfs[map_quad_zip112, map_tri_zip12] >>
 fs[GSYM UNZIP_MAP] >>

 `MAP SND (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list) =
          (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)` by fs[MAP_snd_quad_12_1] >>
 gvs[] >>


 ASSUME_TAC wf_arg_full_implied_2 >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP FST (xdl : (string # d) list))`,
    `(MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `(MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `(MAP (λ(e_,tau_,d_,b_). d_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `(MAP (λ(e_,tau_,d_,b_). tau_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `t_scope_list_g`,
    `gscope`, `t_scope_list`, `scopest`, `(order,f',delta_g,delta_b,delta_x,delta_t)`])) >> gvs[] >> 


(*show that the copyin_abstract is implied by the wfness of args *)


ASSUME_TAC copyin_eq_rw >>


   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP FST (xdl : (string # d) list))`,
    `(MAP (λ(e_,tau_,d_,b_). d_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `(MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list : (e # tau # d # bool) list))`,
    `gscope`,  `scopest`, `scope`])) >> gvs[] >> 

gvs[] >>

Q.EXISTS_TAC `THE(copyin (MAP FST xdl) (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)
            (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list) gscope scopest)` >>
gvs[] >>

Cases_on `copyin (MAP FST xdl) (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)
          (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list) gscope scopest` >| [
	  
IMP_RES_TAC wf_arg_list_NONE2 >>
gvs[] >>
fs[copyin_def]
,

gvs[]

]










,

  (* if we can reduce one of the args, then we should be able to progress e -> e' *)

 DISJ2_TAC >>
 IMP_RES_TAC unred_arg_eq >> 

 (* first show that we can indeed find a map for the function f in the context *)
 ASSUME_TAC tfunn_imp_sig_lookup >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, `order`, `t_scope_list_g`,
   `delta_g`, `delta_b`, `delta_x`,
   `(MAP (λ(e_,tau_,d_,b_).(tau_,d_)) (e_tau_d_b_list : (e # tau # d # bool) list))`,
   `tau'`, `f`])) >> gvs[] >>


 (* now use IH *)

 (* we know that i is less than length of teh list *)

 IMP_RES_TAC unred_arg_index_in_range >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`i`])) >> gvs[] >>


 fs[prog_exp_list_def] >>
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`EL i (MAP (λ(e_,tau_,d_,b_). e_)
   (e_tau_d_b_list : (e # tau # d # bool) list))`])) >> gvs[] >>

 `MEM (EL i (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list))
            (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list)` by fs [EL_MEM] >>
 gvs[] >>

  fs[prog_exp_def] >>
  
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, `t_scope_list_g`,
   `(t_tau_tau (EL i (MAP (λ(e_,tau_,d_,b_). tau_)
   (e_tau_d_b_list : (e # tau # d # bool) list))))`,
   `(EL i (MAP (λ(e_,tau_,d_,b_). b_) (e_tau_d_b_list : (e # tau # d # bool) list)))`,
   `(c0,c1,c2,c3,c4,c5)`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f'`])) >> gvs[] >>
 
  IMP_RES_TAC unred_arg_index_result >| [
  (* if d is in/none, then it shouldn't be a constant in order to reduce it *)
  gvs[] >>

  Q.EXISTS_TAC `framel` >>
  Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list ,
   	        ZIP (LUPDATE e' i (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list) ,
		ZIP (MAP FST xdl,MAP SND xdl)))` >>

  Q.EXISTS_TAC `i` >>
  Q.EXISTS_TAC `e'` >>

 rw[] >| [
 rfs[map_rw_quad, LUPDATE_def]
 ,
 rfs[map_quad_zip112] >>
 fs[GSYM UNZIP_MAP]
 ,
 rfs[map_quad_zip112] >>
 fs[GSYM UNZIP_MAP] >>
 `MAP SND (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list) =
          (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)` by fs[MAP_snd_quad_12_1] >>
 gvs[]
 ,
  rfs[map_quad_zip112] 
 ,
  rfs[map_quad_zip112] 
  ]
,



(* now when d is out, then it shouldn't be an lval to be able to reduce it reduced*)
(* now we do cases on the is_e_lval *)

IMP_RES_TAC notlval_case >| [

 gvs[] >>

  Q.EXISTS_TAC `framel` >>
  Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list ,
   	        ZIP (LUPDATE e' i (MAP (λ(e_,tau_,d_,b_). e_) e_tau_d_b_list) ,
		ZIP (MAP FST xdl,MAP SND xdl)))` >>

  Q.EXISTS_TAC `i` >>
  Q.EXISTS_TAC `e'` >>

 rw[] >| [
 rfs[map_rw_quad, LUPDATE_def]
 ,
 rfs[map_quad_zip112] >>
 fs[GSYM UNZIP_MAP]
 ,
 rfs[map_quad_zip112] >>
 fs[GSYM UNZIP_MAP] >>
 `MAP SND (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) e_tau_d_b_list) =
          (MAP (λ(e_,tau_,d_,b_). d_) e_tau_d_b_list)` by fs[MAP_snd_quad_12_1] >>
 gvs[]
 ,
  rfs[map_quad_zip112] 
 ,
  rfs[map_quad_zip112] 
  ]
,


(* e = e_v *)
gvs[is_const_def] >>
IMP_RES_TAC unred_arg_out_is_lval_imp >>
gvs[is_d_out_def] >>
IMP_RES_TAC ev_not_typed_T
]

]


]



(** 1. first let us show that the function is indeed in the context **)
 (* 1.1 from t_lookup_funn f, we know that there is indeed a map for it in c...  *)
 (* c = (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)        *)

,

(****************)
(*  select      *)
(****************)


SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_select e l s)`` >>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [
   (* case select v l s *)
  gvs[is_const_val_exsist, clause_name_def]
  ,  
  fs[prog_exp_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau_tau tau'`, ` b'`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`])) >>
  gvs[] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>
  gvs[is_const_def]

]


,

(****************)
(*  struct      *)
(****************)



SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_struct l2)`` >>
gvs[]>>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

(* we need show that there can be struct reduction from
e_struct -> e_struct if we can find an unred_mem_index
and
e_struct -> v_struct if all the members are constants
so we start cases on is consts
*)

Cases_on `is_consts (MAP (λ(f_,e_,tau_,b_). (e_)) f_e_tau_b_list)` >| [
(* starting from the left disjuction
   if all members are constsants then we know that
   vl_of_el actually exsists *)
   
 DISJ2_TAC >>

 fs[clause_name_def] >>
 Q.EXISTS_TAC `ZIP(
(MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)
,vl_of_el (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>


 rw[map_distrub]  >> gvs[] >| [

 gvs[map_distrub] >>
 subgoal `! (l:(string#e#tau#bool)list) . MAP (λ(f_,e_,tau_,b_). (f_,e_)) l =
                  ZIP
                 (MAP (λ(f_,e_,tau_,b_). f_) l,
                 MAP (λ(f_,e_,tau_,b_). e_) l)` >- (
  Induct >>
  REPEAT STRIP_TAC >>
   fs [GSYM UNZIP_MAP] >>
   PairCases_on `h` >>
   EVAL_TAC) >> gvs[] >>


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]

,


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]
,


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]

]

,


(* now since the list is not constant, then we know that there is an unred arg somewhere
   with the index i *)
DISJ1_TAC >>
fs[clause_name_def] >>

(* now cases on unred mem arg*)

ASSUME_TAC not_const_unred_mem >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`MAP (λ(f_,e_,tau_,b_). (e_)) (f_e_tau_b_list : (string # e # tau # bool) list)`])) >>
gvs[] >>
RES_TAC >>


fs[prog_strexp_list_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`EL i (MAP (λ(f_,e_,tau_,b_). (e_)) (f_e_tau_b_list : (string # e # tau # bool) list))`])) >>

fs[map_rw_quad, UNZIP_rw] >>
fs[MEM_EL, LENGTH_MAP] >>
`prog_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty` by METIS_TAC [] >>

Q.PAT_X_ASSUM `prog_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty`
( STRIP_ASSUME_TAC o (Q.SPECL [`gscope`,`scopest`, `t_scope_list`, `t_scope_list_g`
, `(t_tau_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`,
`(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
`c`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f`
]) o (SIMP_RULE (srw_ss()) [prog_exp_def])) >>

gvs[] >>


subgoal `¬is_const (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- (
IMP_RES_TAC unred_mem_is_const >>
gvs[]) >> gvs[] >>

 Q.EXISTS_TAC `framel` >>

 Q.EXISTS_TAC `ZIP(
(MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)
,LUPDATE e' i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 Q.EXISTS_TAC `i` >>
 
 Q.EXISTS_TAC `e'` >>



 rw[map_distrub]  >> gvs[] >>


 gvs[map_distrub] >>
 subgoal `! (l:(string#e#tau#bool)list) . MAP (λ(f_,e_,tau_,b_). (f_,e_)) l =
                  ZIP
                 (MAP (λ(f_,e_,tau_,b_). f_) l,
                 MAP (λ(f_,e_,tau_,b_). e_) l)` >- (
  Induct >>
  REPEAT STRIP_TAC >>
   fs [GSYM UNZIP_MAP] >>
   PairCases_on `h` >>
   EVAL_TAC) >> gvs[] >>


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]
]





,

(****************)
(*  header      *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_header b l2)`` >>
gvs[]>>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_red_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>


Cases_on `is_consts (MAP (λ(f_,e_,tau_,b_). (e_)) f_e_tau_b_list)` >| [
(* starting from the left disjuction
   if all members are constsants then we know that
   vl_of_el actually exsists *)
   
 DISJ2_TAC >>

 fs[clause_name_def] >>
 Q.EXISTS_TAC `ZIP(
(MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)
,vl_of_el (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>


 rw[map_distrub]  >> gvs[] >| [

 gvs[map_distrub] >>
 subgoal `! (l:(string#e#tau#bool)list) . MAP (λ(f_,e_,tau_,b_). (f_,e_)) l =
                  ZIP
                 (MAP (λ(f_,e_,tau_,b_). f_) l,
                 MAP (λ(f_,e_,tau_,b_). e_) l)` >- (
  Induct >>
  REPEAT STRIP_TAC >>
   fs [GSYM UNZIP_MAP] >>
   PairCases_on `h` >>
   EVAL_TAC) >> gvs[] >>


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]

,


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]
,


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]

]

,


(* now since the list is not constant, then we know that there is an unred arg somewhere
   with the index i *)
DISJ1_TAC >>
fs[clause_name_def] >>

(* now cases on unred mem arg*)

ASSUME_TAC not_const_unred_mem >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`MAP (λ(f_,e_,tau_,b_). (e_)) (f_e_tau_b_list : (string # e # tau # bool) list)`])) >>
gvs[] >>
RES_TAC >>


fs[prog_strexp_list_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`EL i (MAP (λ(f_,e_,tau_,b_). (e_)) (f_e_tau_b_list : (string # e # tau # bool) list))`])) >>

fs[map_rw_quad, UNZIP_rw] >>
fs[MEM_EL, LENGTH_MAP] >>
`prog_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty` by METIS_TAC [] >>

Q.PAT_X_ASSUM `prog_exp (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)) ty`
( STRIP_ASSUME_TAC o (Q.SPECL [`gscope`,`scopest`, `t_scope_list`, `t_scope_list_g`
, `(t_tau_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`,
`(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
`c`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f`
]) o (SIMP_RULE (srw_ss()) [prog_exp_def])) >>

gvs[] >>


subgoal `¬is_const (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- (
IMP_RES_TAC unred_mem_is_const >>
gvs[]) >> gvs[] >>

 Q.EXISTS_TAC `framel` >>

 Q.EXISTS_TAC `ZIP(
(MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)
,LUPDATE e' i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 Q.EXISTS_TAC `i` >>
 
 Q.EXISTS_TAC `e'` >>



 rw[map_distrub]  >> gvs[] >>


 gvs[map_distrub] >>
 subgoal `! (l:(string#e#tau#bool)list) . MAP (λ(f_,e_,tau_,b_). (f_,e_)) l =
                  ZIP
                 (MAP (λ(f_,e_,tau_,b_). f_) l,
                 MAP (λ(f_,e_,tau_,b_). e_) l)` >- (
  Induct >>
  REPEAT STRIP_TAC >>
   fs [GSYM UNZIP_MAP] >>
   PairCases_on `h` >>
   EVAL_TAC) >> gvs[] >>


 gvs[map_distrub] >>
 fs [GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub]
]




,

(**********************)
(* prog_strexp_list []*)
(**********************)

fsrw_tac [] [prog_strexp_list_def]

,


(**********************)
(* prog_strexp_list   *)
(**********************)

fsrw_tac [] [prog_strexp_list_def, prog_strexp_tup_def] >>
REPEAT STRIP_TAC >>
PairCases_on `tup` >> fs[]

,

(**********************)
(* prog_strexp_tup    *)
(**********************)

fsrw_tac [] [prog_strexp_tup_def]

,

(**********************)
(*  prog_exp_list []  *)
(**********************)

fsrw_tac [] [prog_exp_list_def]

,

(**********************)
(* prog_exp_list      *)
(**********************)

fsrw_tac [] [prog_exp_list_def] >>
REPEAT STRIP_TAC >>
fs[]
]
);
























