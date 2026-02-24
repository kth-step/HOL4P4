open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_deterTheory;
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
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_sem_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_sem_cases] thm)))

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


val _ = new_theory "p4_e_subject_reduction";



val t_passed_elem_def = Define ‘
    t_passed_elem funn delta_g delta_b delta_t t_scope_list_g  =
    ((t_map_to_pass funn delta_b),
     (t_tbl_to_pass funn delta_b delta_t),
     (t_scopes_to_pass funn delta_g delta_b t_scope_list_g))
’;



Theorem WT_c_ec:
!apply_table_f ext_map func_map b_func_map pars_map tbl_map
 get_oracle_index set_oracle_index oracle_index random_oracle
 order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n.
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,
      get_oracle_index,set_oracle_index,random_oracle)
      order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n <=>
WT_ec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,
       oracle_index, random_oracle)
       order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n
Proof
rpt strip_tac >>
gs[WT_c_cases, WT_ec_cases] >>
eq_tac >> (
 rpt strip_tac >> (
  gs[clause_name_def]
 )
)
QED

    
(******   Subject Reduction for expression    ******)
(*t_scopes_consistent is with respect to the expression's global, not the passed, because at that point we are comparing with respect to the passed scope that is already exists in the expression *)

val sr_exp_def = Define `
 sr_exp (e) (ty:'a itself) =
 ! e' gscope (scopest:scope list) framel i_opt t_scope_list t_scope_list_g T_e tau b
      (ec:'a ectx) order delta_g delta_b delta_t delta_x f f_called stmt_called copied_in_scope Prs_n
      apply_table_f ext_map func_map b_func_map pars_map tbl_map oracle_index random_oracle .
       (type_scopes_list  (gscope)  (t_scope_list_g) ) /\
       (type_scopes_list  (scopest) (t_scope_list)) /\
       (star_not_in_sl (scopest)  ) /\
           
       (ec = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map , oracle_index , random_oracle ) ) ∧
       (WT_ec ec order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) /\
       (e_red ec gscope scopest e e' (framel, i_opt) ) /\
       (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e) tau  b) /\
       (T_e = (order,  f, (delta_g, delta_b, delta_x, delta_t))) ==>
            
       ((?b'. (e_typ ( t_scope_list_g  ,  t_scope_list ) T_e (e') tau  b')) /\
              
        (  (framel = [f_called, [stmt_called] , copied_in_scope] ) ==>     
           ? passed_tslg passed_delta_t passed_delta_b passed_gscope t_scope_list_fr .
             order (order_elem_f f_called) (order_elem_f f) ∧      
             t_passed_elem f_called delta_g delta_b delta_t t_scope_list_g = (SOME passed_delta_b,  SOME passed_delta_t , SOME passed_tslg) ∧             
             scopes_to_pass f_called func_map b_func_map gscope = SOME passed_gscope ∧
             t_scopes_consistent T_e (t_scope_list) (t_scope_list_g) (t_scope_list_fr)  ∧
	     frame_typ (passed_tslg,t_scope_list_fr)  (order,  f_called , (delta_g,passed_delta_b, delta_x, passed_delta_t)) Prs_n passed_gscope copied_in_scope [stmt_called] )
            )
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
rpt strip_tac >>
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

rpt strip_tac >>
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

rpt strip_tac >>
OPEN_EXP_TYP_TAC ``e`` >>
fs[] >>
fs[v_of_e_def, is_const_def]
) ;



(*
for a list of expressions l',
if all the list members are constants, then accessing any member is a constant
*)
Theorem EL_consts_is_const:
!l i. i < LENGTH l /\ is_consts (l) ==>
is_const (EL i (l))
Proof
rpt strip_tac >>
fs[is_consts_def] >>
fs[is_const_def] >>
fs[EVERY_EL]
QED




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
rpt strip_tac >>

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
Theorem evl_types_vl_blist:
    ∀l l' l'' i t_scope_list_g t_scope_list T_e.
       LENGTH l = LENGTH l' /\ LENGTH l = LENGTH l'' ∧ i < LENGTH l ∧ is_consts l ∧
       e_typ (t_scope_list_g,t_scope_list) T_e (EL i l) (t_tau (EL i l')) (EL i l'') ⇒
       v_typ (EL i (vl_of_el l)) (t_tau (EL i l')) F
Proof

Induct_on `l` >>
Induct_on `l'` >>
Induct_on `l''` >>
fs[] >>

rpt strip_tac >> 
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
QED





(** similar & similarl theorems **)

(* variable name x cannot be looked up in the scope sc if and only if it cannot be looked up
   in the typing scope tc *)
Theorem R_ALOOKUP_NONE_scopes:
! R v x t sc tc.
 similar R tc sc ==>
((NONE = ALOOKUP sc x)  <=>
(NONE = ALOOKUP tc x ) )
Proof

Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw[ALOOKUP_MEM] >>

rpt strip_tac >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs[similar_def] >>
rw[] >>

LAST_X_ASSUM
( STRIP_ASSUME_TAC o (Q.SPECL [`R`,`x`,`tc`])) >>
fs[similar_def,LIST_REL_def]
QED




(*
TODO: fix the comments everywhere, here the v and t are tuples where teh second element is an lval op
if the variable name is in the scope sc and has the value v , as well as the typing scope tc with the type t , and also we know that tc |- sc, then v : (tau, F)
*)
Theorem R_ALOOKUP_scopes:
! R v x t sc tc.
( similar R tc sc /\
(SOME v = ALOOKUP sc x)   /\
(SOME t = ALOOKUP tc x ) ) ==>
(R t v)
Proof

Induct_on `sc` >>
Induct_on `tc` >>

RW_TAC list_ss [similar_def] >>
rw[ALOOKUP_MEM] >>
FULL_SIMP_TAC list_ss [ALOOKUP_def, ALOOKUP_MEM] >>

rpt strip_tac >>
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
QED



Theorem R_find_topmost_map_scopesl:
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = find_topmost_map tcl x)   /\
(SOME l2 = find_topmost_map scl x ) ) ==>
((similar R (SND l1) (SND l2)) /\ (FST l1 = FST l2) )
Proof


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
QED




Theorem R_topmost_map_scopesl:
! R x l1 l2 scl tcl.
( similarl R tcl scl /\
(SOME l1 = topmost_map tcl x)   /\
(SOME l2 = topmost_map scl x ) ) ==>
(similar R l1 l2)
Proof

simp [topmost_map_def] >>
rpt strip_tac >>

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
QED




Theorem R_lookup_map_scopesl:
! R v x t scl tcl.
( similarl R tcl scl /\
(SOME v = lookup_map scl x)   /\
(SOME t = lookup_map tcl x ) ) ==>
(R t v)
Proof

fs[lookup_map_def] >>
rpt strip_tac >>

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
QED






Theorem type_scopes_list_LENGTH:
! l1 l2 . type_scopes_list l1 l2 ==>
          (LENGTH l1 = LENGTH l2)
Proof
fs[type_scopes_list_def, similarl_def, similar_def] >>
rpt strip_tac >>
IMP_RES_TAC LIST_REL_LENGTH
QED


Theorem type_scopes_list_APPEND:
! l1 l2 l3 l4. type_scopes_list l1 l2 /\
          type_scopes_list l3 l4 ==>
	  type_scopes_list (l1++l3) (l2++l4)
Proof
fs[type_scopes_list_def, similarl_def, similar_def] >>
rpt strip_tac >>
IMP_RES_TAC LIST_REL_APPEND
QED



val varn_is_typed = prove (``
! gsl gtsl sl tsl varn v tau .
          type_scopes_list gsl gtsl ∧
          type_scopes_list sl tsl ∧
          SOME v = lookup_vexp2 sl gsl varn ∧
          SOME tau = lookup_tau tsl gtsl varn ==>
          v_typ v (t_tau tau) F
``,

rpt strip_tac >>
IMP_RES_TAC type_scopes_list_LENGTH >>

fs[lookup_vexp2_def] >>
fs[lookup_tau_def] >>

Cases_on `lookup_map (sl ⧺ gsl) varn` >>
Cases_on `lookup_map (tsl ⧺ gtsl) varn` >>
fs[] >> rw[] >>

subgoal `type_scopes_list (sl ⧺ gsl) (tsl ⧺ gtsl)` >-
IMP_RES_TAC type_scopes_list_APPEND >>

PairCases_on `x` >>
PairCases_on `x'` >> gvs[] >>

fs[type_scopes_list_def] >>
subgoal `∀x t.
          SOME t = lookup_map (sl ⧺ gsl) x ⇒
          ∀v. SOME v = lookup_map (tsl ⧺ gtsl) x ⇒
              (λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2) t v` >-
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

rpt strip_tac >>
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
rpt strip_tac >>
RES_TAC >>
fs[P_NONE_hold]
);


Theorem lookup_map_in_gsl_lemma:
! v lvalop f sl gsl.
SOME (v,lvalop)  = lookup_map (sl ⧺ gsl) (varn_star f) /\
star_not_in_sl sl ==>
SOME (v,lvalop) = lookup_map   gsl (varn_star f)
Proof

rpt strip_tac >>

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
QED





Theorem lookup_in_gsl_lemma:
! v f sl gsl.
SOME v = lookup_vexp2 sl gsl (varn_star f) /\
star_not_in_sl sl ==>
SOME v = lookup_vexp2 [] gsl (varn_star f)
Proof

rpt strip_tac >>
fs[lookup_vexp2_def] >>

Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >> 
Cases_on `lookup_map gsl (varn_star f)` >> fs[] >>
PairCases_on `x` >> fs[] >>

ASSUME_TAC lookup_map_in_gsl_lemma >>
  FIRST_X_ASSUM
  (STRIP_ASSUME_TAC o (Q.SPECL [`v`,`x1`,`f`,`sl`, `gsl`])) >> gvs[]
QED







Theorem lookup_map_none_lemma1:
! t_scope_list_g varn.  LENGTH t_scope_list_g = 2 /\
  lookup_map t_scope_list_g (varn) = NONE ==>
  (ALOOKUP (EL 1 t_scope_list_g) (varn) = NONE /\
   ALOOKUP (EL 0 t_scope_list_g) (varn) = NONE)
Proof
rpt strip_tac >>
fs[lookup_map_def] >>
fs[topmost_map_def] >>
fs[find_topmost_map_def] >>

Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc varn)) t_scope_list_g` >>
fs[] >> rw[] >> FIRST[
  (* first and third subgoals *)
  IMP_RES_TAC index_none_not_every >>
  FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
  fs[EVERY_EL] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[]
  ,
  (* second and fourth subgoals *)
  PairCases_on `x` >>
  fs[] >>
  Cases_on `ALOOKUP x1 varn` >>
  fs[] >> rw[] >>
  fs[INDEX_FIND_EQ_SOME_0]
  ]
QED





val lookup_glb_local_ctx = prove ( ``

! func_map delta_g func_map delta_b b_func_map s stmt_called
xdl txdl ext_map delta_x tau.

dom_tmap_ei delta_g delta_b /\
dom_g_eq delta_g func_map /\
dom_b_eq delta_b b_func_map /\
SOME (stmt_called,xdl) =
        lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map /\
SOME (txdl,tau) = t_lookup_funn (funn_name s) delta_g delta_b delta_x  ==>

((ALOOKUP func_map s = SOME (stmt_called,xdl) /\
 ALOOKUP delta_g s = SOME (txdl,tau) /\
 (ALOOKUP b_func_map s = NONE /\
 ALOOKUP delta_b s = NONE )) \/
 
(ALOOKUP func_map s = NONE /\
 ALOOKUP delta_g s = NONE /\
ALOOKUP b_func_map s = SOME (stmt_called,xdl) /\
 ALOOKUP delta_b s = SOME (txdl,tau)) 
) ``,

rpt strip_tac >>
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




val t_lookup_funn_lemma_old = prove ( ``
! delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn f delta_g [] [] /\
dom_tmap_ei delta_g delta_b ==>
(? tau' txdl' . ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b []) /\
               ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (txdl = txdl' /\ tau = tau'))``,

rpt strip_tac >>
Cases_on `f` >>
fs[t_lookup_funn_def] >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

fs[dom_tmap_ei_def] >>
rfs[dom_empty_intersection_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[]
);

                                    
val t_lookup_funn_lemma = prove ( ``
! delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn f delta_g [] delta_x /\
dom_tmap_ei delta_g delta_b ==>
(? tau' txdl' . ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (txdl = txdl' /\ tau = tau'))``,

rpt strip_tac >>
fs[t_lookup_funn_def] >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

fs[dom_tmap_ei_def] >>
rfs[dom_empty_intersection_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[]
);






                                    

val t_lookup_funn_blk_lemma = prove ( ``
! delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn (f) [] delta_b []  ==>
(? tau' txdl' . ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b []) /\
               ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (txdl = txdl' /\ tau = tau')) ``,

rpt strip_tac >>
Cases_on `f` >>
fs[t_lookup_funn_def] >>
Cases_on `ALOOKUP delta_b s` >>
fs[] >> rw[]
);



Theorem t_lookup_funn_ext_lemma:
! delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn (f) [] [] delta_x ==>
(? tau' txdl' . ( SOME (txdl',tau') = t_lookup_funn f delta_g delta_b delta_x) /\
	       (txdl = txdl' /\ tau = tau'))
Proof         

rpt strip_tac >>
Cases_on `f` >>
fs[t_lookup_funn_def]
QED







val WT_c_imp_global_or_local_lookup = prove ( ``

! func_map delta_g func_map delta_b b_func_map s stmt_called
xdl ext_map delta_x order t_scope_list_g pars_map tbl_map set_oracle_index get_oracle_index random_oracle stmt apply_table_f delta_t Prs_n.
SOME (stmt,xdl) =
        lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map /\
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,set_oracle_index,get_oracle_index,random_oracle)
          order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ==>

((ALOOKUP func_map s = SOME (stmt,xdl) /\
 (? tau txdl . ALOOKUP delta_g s = SOME (txdl,tau)) /\
 (ALOOKUP b_func_map s = NONE /\
 ALOOKUP delta_b s = NONE )) \/
 
(ALOOKUP func_map s = NONE /\
 ALOOKUP delta_g s = NONE /\
ALOOKUP b_func_map s = SOME (stmt,xdl) /\
 (?tau txdl . ALOOKUP delta_b s = SOME (txdl,tau)) 
))
  ``,


rpt strip_tac >>
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


Theorem Fg_star_lemma1:
! t_scope_list_g f func_map delta_g delta_b delta_x order
  b_func_map gscope (ext_map: 'a ext_map)
  stmt xdl apply_table_f pars_map tbl_map set_oracle_index get_oracle_index random_oracle delta_t Prs_n.
  
   type_scopes_list gscope t_scope_list_g ∧
   SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map /\
   WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,set_oracle_index,get_oracle_index,random_oracle)
          order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n
	  ==>
    ( ? tau txdl. SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x /\
    (SOME tau = find_star_in_globals t_scope_list_g (varn_star f)))
Proof

Cases_on `f` >>
rpt strip_tac >| [

  (* global and blk functions *)

 IMP_RES_TAC WT_c_imp_global_or_local_lookup >>
 gvs[] >| [

   fs[WT_c_cases] >>
   gvs[WTFg_cases, func_map_typed_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`, `xdl`, `s`, ‘lol’])) >>
   gvs[] >>
   IMP_RES_TAC t_lookup_funn_lemma_old >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`])) >>
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,
   fs[WT_c_cases] >>
   gvs[WTFb_cases, func_map_blk_typed_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`, `xdl`, `s`, ‘lol’])) >> gvs[] >>
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

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`a`, `g_scope`, `local_scope`])) >> gvs[] >>
        
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
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`a`, `g_scope`, `local_scope`])) >> gvs[] >>
                                   
 IMP_RES_TAC t_lookup_funn_ext_lemma >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`delta_g`,`delta_b`])) >>
 srw_tac [SatisfySimps.SATISFY_ss][]    
]
QED







Theorem Fg_star_lemma2:
! t_scope_list_g f func_map tau delta_g delta_b delta_x order
b_func_map gscope (ext_map: 'a ext_map) tau txdl
  stmt xdl apply_table_f pars_map tbl_map set_oracle_index get_oracle_index random_oracle delta_t Prs_n.
  
   type_scopes_list gscope t_scope_list_g ∧
   
   SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map /\
   
   WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,set_oracle_index,get_oracle_index,random_oracle)
         order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n /\
	 SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ==>
    (? tau' . SOME tau' = find_star_in_globals t_scope_list_g (varn_star f) /\
                   tau = tau' ) 
Proof                   
rpt strip_tac >>
IMP_RES_TAC Fg_star_lemma1 >>
gvs[] >>
Cases_on `t_lookup_funn f delta_g delta_b delta_x` >> rfs[] >>
PairCases_on `x` >> gvs[]
QED




val e_resulted_frame_is_WT = prove ( ``
! (ec:'a ectx) gscope scopest e e' f_called stmt_called copied_in_scope i_opt
             t_scope_list_g t_scope_list order delta_g delta_b delta_x delta_t f (ty:'a itself) b tau
             apply_table_f ext_map func_map b_func_map pars_map tbl_map oracle_index random_oracle Prs_n.
             
    e_red ec gscope scopest e e' ([(f_called,[stmt_called],copied_in_scope)], i_opt) /\
    sr_exp e ty /\
    (ec= (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,oracle_index,random_oracle)) /\      
    type_scopes_list gscope t_scope_list_g /\
    type_scopes_list scopest t_scope_list /\
    star_not_in_sl scopest /\
    (*parseError_in_gs t_scope_list_g  [t_scope_list] ∧ *)            
                   
    e_typ (t_scope_list_g,t_scope_list) (order,f,delta_g,delta_b,delta_x,delta_t) e (tau) b /\
    WT_ec ec order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n
    ==>
    ∃passed_tslg passed_delta_t passed_delta_b passed_gscope t_scope_list_fr.
          order (order_elem_f f_called) (order_elem_f f) ∧
          t_passed_elem f_called delta_g delta_b delta_t t_scope_list_g = (SOME passed_delta_b,SOME passed_delta_t,SOME passed_tslg) ∧
          scopes_to_pass f_called func_map b_func_map gscope = SOME passed_gscope ∧
          t_scopes_consistent (order,f,delta_g,delta_b,delta_x,delta_t) t_scope_list t_scope_list_g t_scope_list_fr ∧
          frame_typ (passed_tslg,t_scope_list_fr) (order,f_called,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n passed_gscope copied_in_scope [stmt_called] ``,

rpt strip_tac >>
gvs[] >>

Q.PAT_X_ASSUM `sr_exp e ty`
((STRIP_ASSUME_TAC o (Q.SPECL
                      [`e'`, `gscope`, `scopest` , `[(f_called,[stmt_called],copied_in_scope)]`, ‘i_opt’, `t_scope_list`, `t_scope_list_g`, `tau`, `b`,
                       `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f`,
                       ‘f_called’, ‘stmt_called’ , ‘copied_in_scope’, ‘Prs_n’,
                       ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’, ‘oracle_index’, ‘random_oracle’])) o SIMP_RULE (srw_ss()) [sr_exp_def]) >>

gvs[] >>
srw_tac [SatisfySimps.SATISFY_ss][]                                     
);



Theorem lookup_funn_t_map_NONE:
! delta_g delta_b delta_x func_map b_func_map ext_map f .
dom_tmap_ei delta_g delta_b /\
dom_g_eq delta_g func_map /\
dom_b_eq delta_b b_func_map /\
dom_x_eq delta_x ext_map  ==>
(t_lookup_funn (f) delta_g delta_b delta_x = NONE <=>
lookup_funn_sig_body (f) func_map b_func_map ext_map = NONE)
Proof

rpt strip_tac >>
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
QED








Theorem tfunn_imp_sig_body_lookup:
! apply_table_f ext_map func_map b_func_map pars_map tbl_map get_oracle_index set_oracle_index random_oracle
  order t_scope_list_g delta_g delta_b delta_x txdl tau f delta_t Prs_n.
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,get_oracle_index,set_oracle_index,random_oracle)
       order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n /\
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x  ==>
?stmt xdl.
    SOME (stmt,xdl) =
    lookup_funn_sig_body f func_map b_func_map ext_map ∧
    MAP (\(t,x,d).d) txdl = MAP SND xdl ∧
    MAP (\(t,x,d).x) txdl = MAP FST xdl ∧                          
    (*not_parseError_str xdl ∧  *)  
    LENGTH (MAP SND xdl) = LENGTH (MAP SND txdl) ∧
    ALL_DISTINCT (MAP FST xdl)
Proof

fs[WT_c_cases] >>
rpt strip_tac >>
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
      ` x1`, ` txdl`, `ext_map`, ` delta_x`, `tau`])) >> gvs[] >| [

     fs[WTFg_cases] >>
     fs[func_map_typed_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`,`x1`, `s`, ‘lol’])) >>
     gvs[same_dir_x_def] >>

     ASSUME_TAC t_lookup_funn_lemma_old >> RES_TAC >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`])) >>
     Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >>
     gvs[] >>


     FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
     FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
     gvs[ELIM_UNCURRY]

     ,
     fs[WTFb_cases] >>
     fs[func_map_blk_typed_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`,`x1`, `s`, ‘lol’])) >>
     gvs[same_dir_x_def] >>

     IMP_RES_TAC t_lookup_funn_blk_lemma >> RES_TAC >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`,`delta_g`])) >>
     Cases_on `t_lookup_funn (funn_name s) delta_g delta_b delta_x` >> gvs[] >>

     FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
     FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
     gvs[ELIM_UNCURRY]
    
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

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`q'`, `s`, `r'`, `x'1`])) >> gvs[] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`a`, `g_scope`, `local_scope`])) >> gvs[] >>


   gvs[same_dir_x_def] >>

   FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
   FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
   gvs[ELIM_UNCURRY]

                       
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

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`$var$(x'0')`, `s`, `s0`, `x'0`, `x'1`, `$var$(x'1')`])) >> gvs[] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`a`, `g_scope`, `local_scope`])) >> gvs[] >>
                                     
   RES_TAC >> gvs[same_dir_x_def] >>

           
   FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
   FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
   gvs[ELIM_UNCURRY]
   ]
 ]
QED








Theorem tfunn_imp_sig_lookup:
! apply_table_f ext_map func_map b_func_map pars_map tbl_map get_oracle_index set_oracle_index random_oracle
  order t_scope_list_g delta_g delta_b delta_x txdl tau f delta_t Prs_n .
    WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,get_oracle_index,set_oracle_index,random_oracle)
          order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n /\
    SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ==>
            ? xdl.
            SOME xdl = lookup_funn_sig f func_map b_func_map ext_map /\
            MAP (λ(t,x,d). d) txdl = MAP SND xdl /\
            LENGTH (MAP SND xdl) = LENGTH (MAP SND txdl) /\
            ALL_DISTINCT (MAP FST xdl)  
Proof

rpt strip_tac >>
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
QED









val out_is_val_imp_every = prove (``
 ! dl bl .
   out_is_lval dl bl ==>
   EVERY (\ (dir,b) . is_d_out dir ==> b ) (ZIP(dl, bl))``,

fs[out_is_lval_def] >>
fs[EVERY_EL] >>
Induct_on `bl` >>
Induct_on `dl` >>
gvs[] >>
rpt strip_tac >>
Cases_on `n` >| [

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
 fs[EL_CONS]
 ,
 fs[EL_CONS] >>
 fs[PRE_SUB1] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`dl`])) >>

  subgoal `∀i. i < LENGTH dl ⇒ is_d_out (EL i (dl)) ⇒ EL i (bl)` >-
  ( NTAC 2 STRIP_TAC >>
    Q.PAT_X_ASSUM `∀i. i < SUC (LENGTH dl) ⇒ is_d_out (EL i (h::dl)) ⇒ EL i (h'::bl)`
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
rpt strip_tac >| [
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
rpt strip_tac >>
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


    

Theorem unred_arg_index_result:
! dl el i .
unred_arg_index dl el = SOME i ⇒
       ¬is_d_out (EL i dl) ∧ ¬is_const (EL i el) ∨
       is_d_out (EL i dl) ∧ ¬is_e_lval (EL i el)
Proof       

NTAC 4 STRIP_TAC >> 
IMP_RES_TAC unred_arg_index_details >>
SRW_TAC [] [unred_arg_index_details, is_d_out_def] 
QED





                    
val unred_arg_index_in_range2 = prove ( “
∀dl el i. unred_arg_index dl el = SOME i ⇒ i < LENGTH dl
                                      ”,
 rpt strip_tac >>
 fs[unred_arg_index_def] >>
 fs[find_unred_arg_def] >>
 Cases_on `INDEX_FIND 0 (λ(d,e). ¬is_arg_red d e) (ZIP (dl,el))` >> 
 gvs [] >>
 Cases_on `x` >>
 IMP_RES_TAC index_find_length >>
 fs []
);        


                        

Theorem unred_arg_out_is_lval_imp:
∀i dl bl el.
unred_arg_index dl el = SOME i ∧ out_is_lval dl bl ⇒
            EL i bl ∨ EL i dl = d_none ∨ EL i dl = d_in
Proof             
rpt strip_tac >>
IMP_RES_TAC unred_arg_index_details>>
fs[out_is_lval_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
fs[is_d_out_def] >>

IMP_RES_TAC unred_arg_index_in_range2 >>
fs[is_d_out_def]               
QED




val dir_fun_delta_same = prove ( ``
! xdl txdl ftau f func_map b_func_map ext_map delta_g delta_b delta_x
apply_table_f order t_scope_list_g pars_map tbl_map get_oracle_index
set_oracle_index random_oracle delta_t  Prs_n. 
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,get_oracle_index,set_oracle_index,random_oracle)
          order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n /\
SOME (xdl) = lookup_funn_sig f func_map b_func_map ext_map /\
SOME (txdl, ftau) = t_lookup_funn f delta_g delta_b delta_x  ==>
MAP (λ(t,x,d). d) txdl = MAP SND xdl ``,

rpt strip_tac  >>
IMP_RES_TAC tfunn_imp_sig_lookup >>
gvs[] >>
Cases_on `lookup_funn_sig f func_map b_func_map ext_map` >> rfs[]
);







val two_lookup_funn = prove ( ``
! f delta_g delta_b delta_x tau tau' txdl txdl'.
SOME (txdl,tau) = t_lookup_funn (f) delta_g delta_b delta_x /\
SOME (txdl',tau') = t_lookup_funn (f) delta_g delta_b delta_x ==>
	(tau = tau') /\ (txdl= txdl') ``,

rpt strip_tac >>
Cases_on `t_lookup_funn f delta_g delta_b delta_x` >> gvs[]
);



Theorem e_lval_tlval:
!e b t_scope_list t_scope_list_g tau T_e.
e_typ (t_scope_list_g,t_scope_list) T_e  e tau b
	  ==> b ==> is_e_lval (e)
Proof

Induct >> 

rpt strip_tac >~ [`is_e_lval (e_acc e s)`] >-
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
QED




(** context related theorems **)


val trans_names_imp = prove ( ``
! l Prs_n . 
literials_in_P_state l ["accept"; "reject"] ==>
literials_in_P_state l (Prs_n ⧺ ["accept"; "reject"]) ``,

fs[literials_in_P_state_def] >>
Induct >>
fs[]
);



(*we need to show that the statement that we get is always extern
  the scope is well typed and it is always well typed*)

val funn_inst_ext_prod_ext_stmt = prove ( ``
! f s s' stmt xdl func_map b_func_map ext_map .
(f = funn_inst s \/ f = (funn_ext s s')) /\
SOME (stmt,xdl) = lookup_funn_sig_body (f) func_map b_func_map ext_map ==>
stmt= stmt_ext
``,

rpt strip_tac >>
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


Theorem dom_eq_imp_NONE:
∀ delta_g func_map delta_b b_func_map s.
(dom_g_eq delta_g func_map ⇒
(ALOOKUP delta_g s = NONE ⇔ ALOOKUP func_map s = NONE))
∧
(dom_b_eq delta_b b_func_map ⇒
(ALOOKUP delta_b s = NONE ⇔ ALOOKUP b_func_map s = NONE))
Proof

         
rpt strip_tac >| [         
gvs[dom_g_eq_def, dom_eq_def, is_lookup_defined_def]>>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
Cases_on ‘ALOOKUP delta_g s’ >> gvs[] >>
Cases_on ‘ALOOKUP func_map s’ >> gvs[]
,
gvs[dom_b_eq_def, dom_eq_def, is_lookup_defined_def]>>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>
Cases_on ‘ALOOKUP delta_b s’ >> gvs[] >>
Cases_on ‘ALOOKUP b_func_map s’ >> gvs[]
]   
QED         



val func_lookup_cases_eq = prove (“           
∀ func_map b_func_map ext_map stmt stmt' xdl xdl' s.
( lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map = SOME (stmt,xdl) ∧
  ALOOKUP func_map s = SOME  (stmt',xdl') ∧ 
  ALOOKUP b_func_map s = NONE ⇒
       ((stmt,xdl) = (stmt',xdl'))  )
∧

( lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map = SOME (stmt,xdl) ∧
  ALOOKUP func_map s = NONE ∧ 
  ALOOKUP b_func_map s = SOME  (stmt',xdl') ⇒
       ((stmt,xdl) = (stmt',xdl'))  )”,
  
rpt strip_tac>>            
gvs[lookup_funn_sig_body_def]
);




           

val all_func_maps_contains_welltyped_body_min = prove ( ``

! xdl txdl el stmt tau f
  (ext_map:'a ext_map) func_map b_func_map order t_scope_list_g
            delta_g delta_b delta_x delta_t gscope Prs_n.
        dom_tmap_ei delta_g delta_b ∧ dom_g_eq delta_g func_map ∧
        dom_b_eq delta_b b_func_map ∧ typying_domains_ei delta_g delta_b delta_x ∧
        WTFg func_map order t_scope_list_g delta_g delta_b delta_x Prs_n ∧
        WTFb b_func_map order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n  ∧
             
MAP (λ(t,x,d). d) txdl = MAP SND xdl /\
MAP (λ(t,x,d). x) txdl = MAP FST xdl /\

LENGTH txdl = LENGTH xdl /\
LENGTH el = LENGTH xdl ∧
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x /\	
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map ==>

 ∃passed_tslg passed_delta_t passed_delta_b passed_gscope.
          (t_map_to_pass f delta_b = SOME passed_delta_b ∧
           t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧
           t_scopes_to_pass f delta_g delta_b t_scope_list_g = SOME passed_tslg) ∧
          scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
          t_lookup_funn f delta_g delta_b delta_x = t_lookup_funn f delta_g passed_delta_b delta_x ∧
         
stmt_typ (passed_tslg, [ZIP (mk_varn (MAP FST xdl), ZIP (MAP FST txdl,  MAP (\e. get_lval_of_e e) el)) ])
          (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n stmt
``,

rpt strip_tac >>

Cases_on `f` >>
gvs[t_map_to_pass_def, t_tbl_to_pass_def, t_scopes_to_pass_def, t_lookup_funn_def, scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])>> 

IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >| [
(* global functions *)

  fs[WTFg_cases] >>
  fs[func_map_typed_def] >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`,`xdl `,`s`, ‘MAP (λe. get_lval_of_e e) el’])) >>
  gvs[] >>
  Cases_on ‘lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map’ >> gvs[] >>
  ‘x' = (stmt,xdl)’ by  (PairCases_on ‘x'’ >>    IMP_RES_TAC func_lookup_cases_eq >> gvs[] ) >>
  gvs[] >>
  gvs[t_scopes_to_pass_def, mk_tscope_def] >>
  subgoal ‘tau = r ∧ q = txdl ’ >- (rfs[t_lookup_funn_def]) >> gvs[] >>
  subgoal ‘MAP (λ(t,x,d). t) q = MAP FST q’ >- (gvs[ELIM_UNCURRY, map_fst_EQ]) >>
  gvs[]        
  ,
        
  fs[WTFb_cases] >>
  fs[func_map_blk_typed_def] >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt`,`xdl `,`s`, ‘MAP (λe. get_lval_of_e e) el’])) >>
  gvs[] >>
  Cases_on ‘lookup_funn_sig_body (funn_name s) func_map b_func_map ext_map’ >> gvs[] >>
  ‘x' = (stmt,xdl)’ by  (PairCases_on ‘x'’ >>    IMP_RES_TAC func_lookup_cases_eq >> gvs[] ) >>
  gvs[] >>
  gvs[t_scopes_to_pass_def, mk_tscope_def] >>
  subgoal ‘tau = r ∧ q = txdl ’ >- (rfs[t_lookup_funn_def]) >> gvs[] >>
  subgoal ‘MAP (λ(t,x,d). t) q = MAP FST q’ >- (gvs[ELIM_UNCURRY, map_fst_EQ]) >>
  gvs[] 
                            
  ,
        
  gvs[dom_tmap_ei_def, typying_domains_ei_def, dom_empty_intersection_def] >>
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[])
  ,
  
         (* funn inst s *)
  IMP_RES_TAC funn_inst_ext_prod_ext_stmt >>
  srw_tac [SatisfySimps.SATISFY_ss] [Once stmt_typ_cases, clause_name_def] >>
  gvs[ext_is_defined_def, ext_not_defined_def] >>
  gvs[lookup_funn_sig_body_def] >>
  REPEAT BasicProvers.FULL_CASE_TAC >> gvs[typying_domains_ei_def, dom_empty_intersection_def] >> 
  REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[])
                  
  ,
  (* funn ext s s' *)
  IMP_RES_TAC funn_inst_ext_prod_ext_stmt >>
  srw_tac [SatisfySimps.SATISFY_ss] [Once stmt_typ_cases, clause_name_def] >>
  gvs[ext_is_defined_def, ext_not_defined_def] >>
  gvs[lookup_funn_sig_body_def] >>
  REPEAT BasicProvers.FULL_CASE_TAC >> gvs[typying_domains_ei_def, dom_empty_intersection_def] >> 
  REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[])
                                  
]
);



val all_func_maps_contains_welltyped_body = prove ( ``

! xdl txdl stmt tau f apply_table_f  (ext_map: 'a ext_map) func_map b_func_map pars_map
       tbl_map order t_scope_list_g delta_g delta_b delta_x delta_t gscope Prs_n el .
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     order t_scope_list_g delta_g delta_b delta_x delta_t  Prs_n /\
     
MAP (λ(t,x,d). d) txdl = MAP SND xdl /\
MAP (λ(t,x,d). x) txdl = MAP FST xdl /\
    
LENGTH txdl = LENGTH xdl /\
LENGTH el = LENGTH xdl ∧

       
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x /\	
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map ==>

 ∃passed_tslg passed_delta_t passed_delta_b passed_gscope.
          (t_map_to_pass f delta_b = SOME passed_delta_b ∧
           t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧
           t_scopes_to_pass f delta_g delta_b t_scope_list_g = SOME passed_tslg) ∧
          scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
          t_lookup_funn f delta_g delta_b delta_x = t_lookup_funn f delta_g passed_delta_b delta_x ∧
         
stmt_typ (passed_tslg, [ZIP (mk_varn (MAP FST xdl), ZIP (MAP FST txdl,  MAP (\e. get_lval_of_e e) el)) ])
          (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n stmt
``,

 fs[WT_c_cases] >>
 rpt strip_tac >>
 drule all_func_maps_contains_welltyped_body_min >>
 rpt strip_tac >>
 RES_TAC >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`])) >>
 srw_tac [SatisfySimps.SATISFY_ss][]
);






        

(** copyin abstraction theorems **)


Definition copyin_abstract_def:
 copyin_abstract xlist dlist elist (ss:scope list) (scope:scope) random_oracle =
  ((! i. ( i < LENGTH xlist)==>
  ((!oracle_index. IS_SOME(one_arg_val_for_newscope (EL i dlist) (EL i elist) ss oracle_index random_oracle)) /\
  ?oracle_index'.
  EL i scope = (varn_name (EL i xlist) , (\ ((a,b),c). (a,c)) $ THE (one_arg_val_for_newscope (EL i dlist) (EL i elist) ss oracle_index' random_oracle)) /\
  LENGTH scope = LENGTH xlist)) /\
  ((LENGTH xlist = 0) ==> scope = []))
End


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
!ss d x e i random_oracle.
   wf_arg d x e ss ⇒
    update_arg_for_newscope ss random_oracle (SOME ([], i)) (d,x,e) =
    (
    let ( (v,i'), lval_opt) = THE (one_arg_val_for_newscope d e ss i random_oracle) in
    SOME ([(varn_name x, (v,lval_opt))], i')

    )
``,
  
fs[wf_arg_def] >>
rpt strip_tac >>
Cases_on `d` >>
fs[is_d_out_def] >>

fs[update_arg_for_newscope_def,
one_arg_val_for_newscope_def] >>
fs[is_d_out_def, is_d_in_def] >>
fs[AUPDATE_def, AllCaseEqs()] >>
Cases_on ‘init_out_v random_oracle i v’ >>
qexistsl_tac [‘q’, ‘r’] >>
gs[]
);



val update_args_none = prove ( ``
! dxel scope ss random_oracle.
~ (FOLDL (update_arg_for_newscope ss random_oracle) NONE (dxel) = SOME scope)
``,

Induct_on `dxel` >>
fs[update_arg_for_newscope_def] >>
REPEAT GEN_TAC >>
PairCases_on `h` >>
EVAL_TAC >>
gvs[]
);




Theorem wf_arg_normalization:
! d dl x xl e el ss.
wf_arg_list (d::dl) (x::xl) (e::el) ss ==>
wf_arg d x e ss /\ wf_arg_list (dl) (xl) (el) ss
Proof
rpt strip_tac >>
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
QED





val wf_arg_list_normalization_imp1 = prove ( ``
! dxel d x e ss .
(wf_arg_list (MAP (λ(d,x,e). d) dxel) (MAP (λ(d,x,e). x) dxel)
          (MAP (λ(d,x,e). e) dxel) ss /\
 wf_arg_list [d] [x] [e] ss) ==>
(wf_arg_list (MAP (λ(d,x,e). d) dxel ⧺ [d])
              (MAP (λ(d,x,e). x) dxel ⧺ [x])
	      (MAP (λ(d,x,e). e) dxel ⧺ [e]) ss ) ``,

SIMP_TAC list_ss [wf_arg_list_def] >>
rpt strip_tac >>
Cases_on `dxel = []` >| [
 gvs[]
 ,


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
rpt strip_tac >| [
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
 rpt strip_tac >>
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
! ss d s e random_oracle i.
 wf_arg d s e ss ==> 
   ~ (update_arg_for_newscope ss random_oracle (SOME ([], i)) (d,s,e) = NONE )
``,

fs[wf_arg_def, update_arg_for_newscope_def, one_arg_val_for_newscope_def] >>
rpt strip_tac >>
Cases_on `is_d_out d` >> (
 gs[AllCaseEqs()]
)
);




Theorem wf_imp_val_lval:
! ss d s e i random_oracle.
 wf_arg d s e ss ==> 
  ? v i' lval_op . one_arg_val_for_newscope d e ss i random_oracle = SOME ((v,i') , lval_op)
Proof
fs[wf_arg_def, one_arg_val_for_newscope_def] >>
rpt strip_tac >>
Cases_on `is_d_out d` >> (fs[]) >>
Cases_on `is_d_in d` >>
fs[is_d_in_def, is_d_out_def] >> rw[] >>
Cases_on ‘init_out_v random_oracle i v’ >>
metis_tac[]
QED





val EL_domain_ci_same = prove (``
!dxel scope ss i random_oracle.
i < LENGTH scope /\
LENGTH scope = LENGTH dxel /\
copyin_abstract (MAP (λ(d,x,e). x) dxel)
                (MAP (λ(d,x,e). d) dxel)
	        (MAP (λ(d,x,e). e) dxel) ss scope random_oracle ==>
   FST (EL i scope) = (varn_name (EL i (MAP (λ(d,x,e). x) dxel)) )``,
simp[copyin_abstract_def] >>
rpt strip_tac >>
gs[] >>
‘i < LENGTH dxel’ by gs[] >>
res_tac >>
gvs[]
);




Theorem wf_arg_list_NONE:
       ! dxel x d e ss i random_oracle.
       ALL_DISTINCT (MAP (λ(d,x,e). x) dxel )  /\
       (wf_arg_list (MAP (λ(d,x,e). d) dxel )
                    (MAP (λ(d,x,e). x) dxel )
		    (MAP (λ(d,x,e). e) dxel ) ss) ==>
      ~ (FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) dxel = NONE)
Proof
HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC]  >>
fs[SNOC_APPEND] >>
PairCases_on `x` >>
fs[] >>
`ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
IMP_RES_TAC wf_arg_list_normalization_imp2 >>
gvs[] >>
RES_TAC >>
Cases_on `FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) dxel` >- (
 SIMP_TAC list_ss [update_arg_for_newscope_def] >>
 IMP_RES_TAC wf_imp_val_lval >>
 gvs[]
) >> 
SIMP_TAC list_ss [update_arg_for_newscope_def] >>
IMP_RES_TAC wf_imp_val_lval >>
PairCases_on ‘x’ >>
qpat_x_assum ‘!random_oracle. _’ (fn thm => assume_tac $ Q.SPECL [‘random_oracle’, ‘x1'’] thm) >>
gs[]
QED
 



val args_ci_scope_LENGTH = prove (``
! dxel ss scope random_oracle.
copyin_abstract (MAP (λ(d,x,e). x) (dxel))
                (MAP (λ(d,x,e). d) (dxel))
		(MAP (λ(d,x,e). e) (dxel)) ss scope random_oracle ==>
		(LENGTH scope = LENGTH dxel)``,
Induct >>
rpt strip_tac >>
fs[copyin_abstract_def] >>
INST_FST [`0`]
);



val args_ci_scope_LENGTH2 = prove ( ``
! xl dl el ss scope random_oracle.
LENGTH xl = LENGTH dl /\ LENGTH xl = LENGTH el /\
copyin_abstract (xl) (dl) (el) ss scope random_oracle ==>
		(LENGTH scope = LENGTH xl)``,
Induct >>
rpt strip_tac >>
fs[copyin_abstract_def] >>
INST_FST [`0`]
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
rpt strip_tac >>
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





Theorem copyin_abstract_normalize_tmp[local]:
!xl dl el  x d e ss scope random_oracle.
LENGTH xl = LENGTH dl /\
LENGTH xl = LENGTH el /\
copyin_abstract (x::xl)
          (d::dl) (e::el) ss scope random_oracle ==>
(copyin_abstract [x] [d] [e] ss [HD scope] random_oracle /\
 copyin_abstract xl dl el ss (TL scope) random_oracle)
Proof
Induct_on `xl` >>
Induct_on `el` >>
Induct_on `dl` >>
fs[] >| [
 fs[copyin_abstract_def] >>
 rpt strip_tac >> (
  INST_FST [`oracle_index`] >>
  Cases_on `scope` >> fs[] >> metis_tac[]
 ),

 rpt strip_tac >| [
  fs[copyin_abstract_def] >>
  rpt strip_tac >>
  INST_FST [`0`] >>
  metis_tac[],

  gvs[] >>
  IMP_RES_TAC args_ci_scope_LENGTH2 >> gvs[] >>
  Cases_on `scope = []` >> (fs[]) >>
  simp[copyin_abstract_def] >>
  NTAC 2 STRIP_TAC >>

  fs[Once EL_compute] >>
  CASE_TAC >> (
   fs[EL_CONS, copyin_abstract_def]
  ) >| [
   qpat_x_assum ‘!i'. _’ (fn thm => assume_tac $ Q.SPECL [‘1’] thm) >>
   rfs[] >>
   qexists_tac ‘oracle_index'’ >>
   rfs[] >>
   Cases_on `scope` >> fs[],

   `i + 1 < LENGTH xl + 2` by fs[] >>
   gs[EL_CONS, PRE_SUB1] >>
   Cases_on `scope` >> fs[] >>
   Cases_on `i = 1` >> fs[] >- (
    qpat_x_assum ‘!i'. _’ (fn thm => assume_tac $ Q.SPECL [‘2’] thm) >>
    gs[] >>
    metis_tac[]
   ) >>
   qpat_x_assum ‘!i'. _’ (fn thm => assume_tac $ Q.SPECL [‘i + 1’] thm) >>
   `i + 1 < LENGTH dl + 2` by fs[] >>
   gs[EL_CONS, PRE_SUB1] >>
   metis_tac[]
  ]
 ]
]
QED




(* simplify it later, it works without the induction *)
Theorem copyin_abstract_normalize[local]:
!dxel x d e ss scope random_oracle.
copyin_abstract (x::MAP (λ(d,x,e). x) (dxel))
                (d::MAP (λ(d,x,e). d) (dxel))
		(e::MAP (λ(d,x,e). e) (dxel)) ss scope random_oracle ==>
   (copyin_abstract [x] [d] [e] ss ([HD scope]) random_oracle /\
    copyin_abstract (MAP (λ(d,x,e). x) (dxel))
          (MAP (λ(d,x,e). d) (dxel)) (MAP (λ(d,x,e). e) (dxel)) ss (TL scope) random_oracle)
Proof
Induct >>
rpt strip_tac >| [
 Cases_on `scope` >> (fs[copyin_abstract_def]) >>
 metis_tac[],
 
 Cases_on `scope` >> (fs[copyin_abstract_def]) >>
 metis_tac[],
 
 fs[copyin_abstract_def] >>
 INST_FST [`0`] >>
 metis_tac[],
 
 fs[copyin_abstract_def] >>
 NTAC 2 strip_tac >>
 INST_FST [`i+1`] >>
 gs[] >>
 strip_tac >- (
  strip_tac >>
  INST_FST [‘oracle_index’] >>
  gs[EL_CONS, PRE_SUB1]
 ) >>
 qexists_tac ‘oracle_index'’ >>
 Cases_on `scope` >> fs[] >>
 gs[EL_CONS, PRE_SUB1]
]
QED




val copyin_abstract_single = prove (``
! x d e ss scope random_oracle.
copyin_abstract [x] [d] [e] ss [HD scope] random_oracle ==>
(ALL_DISTINCT (MAP FST [HD scope]) /\
 FST (HD scope) = varn_name x)
``,

rpt strip_tac >>
IMP_RES_TAC args_ci_scope_LENGTH2 >>
fs[copyin_abstract_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘random_oracle’])) >> fs[]
);



Theorem mk_varn_lemma:
! xl s. ~ MEM (s) xl ==>
        ~ MEM (varn_name s) (mk_varn (xl))
Proof
Induct >> fs[mk_varn_def]
QED


Theorem mk_varn_lemma2:
!l h. mk_varn (h::l) = (varn_name h)::mk_varn l
Proof
Induct_on `l` >> fs[mk_varn_def]
QED



val copyin_abstract_domain = prove ( ``
!dxel ss scope random_oracle.
copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
          (MAP (λ(d,x,e). e) dxel) ss scope random_oracle ==>
           MAP FST scope = mk_varn (MAP (λ(d,x,e). x) dxel)
``,
Induct >- (
 fs[copyin_abstract_def, mk_varn_def]
) >>
rpt strip_tac >>
PairCases_on `h` >>
fs[] >>
IMP_RES_TAC copyin_abstract_normalize >>
fs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`ss`, `TL (scope : (varn # v # lval option) list)`, ‘random_oracle’])) >> gvs[] >>
IMP_RES_TAC copyin_abstract_single >>
fs[mk_varn_lemma2] >>
Cases_on `scope` >> fs[mk_varn_def, copyin_abstract_def]
);



Theorem mk_varn_lemma3:
! xl . 
ALL_DISTINCT (xl) ==>
ALL_DISTINCT (mk_varn (xl))
Proof
Induct >- fs[mk_varn_def] >>
rpt strip_tac >>
gvs[mk_varn_lemma, mk_varn_lemma2]
QED


        

Theorem mk_varn_lemma4:
! xl l. 
  LENGTH xl = LENGTH l ⇒
MAP (λ(a_,b_). b_) (ZIP (mk_varn xl, l)) = l
Proof
Induct_on ‘xl’ >>
Induct_on ‘l’ >> gvs[] >| [
 fs[mk_varn_def]
 ,
 rpt strip_tac >>
 gvs[mk_varn_lemma, mk_varn_lemma2]
 ]
QED                           




Theorem mk_varn_LENGTH:
! xl . LENGTH (mk_varn xl) = LENGTH xl
Proof
Induct_on ‘xl’ >>
fs[mk_varn_def]
QED










                              

(* if all the domain is distict, then if we find something in there,
it should notmbe as the tail of it *)
val copyin_abstract_distinct =  prove (``
! dxel ss x random_oracle.
 ALL_DISTINCT (MAP (λ(d,x,e). x) dxel) /\
 copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel) ss x random_oracle ==>
ALL_DISTINCT (MAP FST x)	  
``,
rpt strip_tac >>

IMP_RES_TAC copyin_abstract_domain >>
`ALL_DISTINCT (MAP FST x) = ALL_DISTINCT (mk_varn (MAP (λ(d,x,e). x) dxel))` by fs[] >>
rw[] >>
gvs[mk_varn_lemma3]
);




val copyin_abstract_distinct_app =  prove (``
! dxel ss x a random_oracle.
ALL_DISTINCT ((MAP (λ(d,x,e). x) dxel) ++ [a] )/\
 copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel) ss x random_oracle ==>
 ALL_DISTINCT ((MAP FST x) ++ [varn_name a] )
``,
rpt strip_tac >>
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

rpt strip_tac >>
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
rpt strip_tac >>

PairCases_on `h` >>
Cases_on `h0 = varn_name x` >> fs[]
);






Theorem copyin_abstract_verbose[local]:
!dxel ss scope i random_oracle.
 (ALL_DISTINCT (MAP (\(d,x,e).x) dxel)) ==>
 (wf_arg_list
  (MAP (λ(d,x,e). d) dxel)
  (MAP (λ(d,x,e). x) dxel)
  (MAP (λ(d,x,e). e) dxel) ss) ==>
 (?i'. (FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) dxel) =
  SOME (scope, i')) ==>
 copyin_abstract (MAP (λ(d,x,e). x) dxel) (MAP (λ(d,x,e). d) dxel) (MAP (λ(d,x,e). e) dxel) ss scope random_oracle
Proof
HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC] >- (
 fs[copyin_abstract_def, wf_arg_list_def]
) >>
fs[SNOC_APPEND] >>
PairCases_on `x` >>
gs[update_arg_for_newscope_def] >>
Cases_on `FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) dxel` >> (fs[]) >>
PairCases_on ‘x’ >>
gvs[AllCaseEqs()] >>
`ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
`ALL_DISTINCT [x1]` by fs[ALL_DISTINCT_APPEND] >>
IMP_RES_TAC wf_arg_list_normalization_imp2 >> gvs[] >>
RES_TAC >>
IMP_RES_TAC wf_imp_val_lval >> fs[] >>
SIMP_TAC list_ss [copyin_abstract_def] >>
NTAC 2 STRIP_TAC >>
Cases_on `i'' = (LENGTH dxel)` >| [
 (* i'' = LENGTH dxel case *)
 rfs[EL_LENGTH_simp] >>
 gvs[] >>
 IMP_RES_TAC args_ci_scope_LENGTH >>
 fs[AUPDATE_def] >>
 strip_tac >- (
  strip_tac >>
  qpat_x_assum ‘!random_oracle. _’ (fn thm => assume_tac $ Q.SPECL [‘random_oracle’, ‘oracle_index’] thm) >>
  gs[]
 ) >>
 Cases_on `ALOOKUP x0' (varn_name x1)` >| [
  (*Cases lookup is NONE *)
  qexists_tac ‘x1'’ >>
  `EL (LENGTH x0') (x0' ⧺ [(varn_name x1,v,lval_opt)]) =
   (varn_name x1,v,lval_opt) ` by fs[EL_LENGTH_simp] >>
  gs[],

  `EL (LENGTH x0') (x0' ⧺ [(varn_name x1,v,lval_op)]) =
   (varn_name x1,v,lval_op) ` by fs[EL_LENGTH_simp] >>
  gs[] >>
  IMP_RES_TAC copyin_abstract_distinct_app >>
  IMP_RES_TAC distinct_not_neg
 ],

 (* i'' ≠ LENGTH dxel /\ i'' < LENGTH dxel case*)
 
 (* This should not be true at all, since we start
    from a distict xlist we should end up in a distict
    scope, which means that we can never find the variable *)  

 fs[] >>
 `i'' < LENGTH dxel` by fs[] >>

 (* sould stay here, because we extract the definition
 of copyin_abstract in the next step, we cannot infer it later *)
 IMP_RES_TAC copyin_abstract_distinct_app >>

 fs[copyin_abstract_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [‘random_oracle’, `i''`])) >>  

 qpat_x_assum ‘!i. i < LENGTH dxel ==> _’ (fn thm => imp_res_tac thm) >>

 (* show that the element is i in the list  *)

 `((EL i'' (MAP (λ(d,x,e). e) dxel) = EL i'' (MAP (λ(d,x,e). e) dxel ⧺ [x2])))` by FULL_SIMP_TAC list_ss [EL_APPEND1] >>

 `((EL i'' (MAP (λ(d,x,e). d) dxel) = EL i'' (MAP (λ(d,x,e). d) dxel ⧺ [x0])))` by FULL_SIMP_TAC list_ss [Once EL_APPEND1] >>

 `((EL i'' (MAP (λ(d,x,e). x) dxel) = EL i'' (MAP (λ(d,x,e). x) dxel ⧺ [x1])))` by FULL_SIMP_TAC list_ss [Once EL_APPEND1] >>


 Cases_on `one_arg_val_for_newscope (EL i'' (MAP (λ(d,x,e). d) dxel ⧺ [x0]))
           (EL i'' (MAP (λ(d,x,e). e) dxel ⧺ [x2])) ss oracle_index' random_oracle` >- (
  INST_FST [‘oracle_index'’] >>
  gs[]
 ) >>
 gs[] >>
 qexists_tac ‘oracle_index'’ >>
 gvs[] >>
 fs[AUPDATE_def] >>
 Cases_on `ALOOKUP x0' (varn_name x1)` >>
 fs[] >|[
  FULL_SIMP_TAC list_ss [] >>
  qpat_x_assum ‘EL i'' x0' = _’ (fn thm => assume_tac $ GSYM thm) >>
  gs[] >>
  ‘i'' < LENGTH x0'’ suffices_by simp[EL_APPEND1] >>
  gs[],

  IMP_RES_TAC distinct_not_neg_in_bound
 ]
]
QED

Theorem all_arg_update_imp[local]:
!dxel ss scope i random_oracle.
 (ALL_DISTINCT (MAP (\(d,x,e).x) dxel)) ==>
 (wf_arg_list
  (MAP (\(d,x,e).d) dxel)
  (MAP (\(d,x,e).x) dxel)
  (MAP (\(d,x,e).e) dxel) ss) ==>
 (?i'. (all_arg_update_for_newscope (MAP (\(d,x,e).x) dxel) (MAP (\(d,x,e).d) dxel) (MAP (\(d,x,e).e) dxel) ss i random_oracle = SOME (scope,i')))
==>
copyin_abstract (MAP (\(d,x,e).x) dxel) (MAP (\(d,x,e).d) dxel) (MAP (\(d,x,e).e) dxel) ss scope random_oracle
Proof
metis_tac[copyin_abstract_verbose, all_arg_update_for_newscope_def, zipped_list]
QED



Theorem copyin_imp:
!e_x_d_list gscope scopest scope i random_oracle.
     (ALL_DISTINCT (MAP (λ(e,x,d). x) e_x_d_list)) ∧
     (wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
                  (MAP (λ(e,x,d). x) e_x_d_list)
		  (MAP (λ(e,x,d). e) e_x_d_list)
                  (scopest ⧺ gscope))  ==>
(
(?i_opt. SOME (scope, i_opt) = copyin (MAP (λ(e,x,d). x) e_x_d_list)
        (MAP (λ(e,x,d). d) e_x_d_list)
	(MAP (λ(e,x,d). e) e_x_d_list) gscope scopest i random_oracle)
==>
copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
                (MAP (λ(e,x,d). d) e_x_d_list)
		(MAP (λ(e,x,d). e) e_x_d_list) (scopest ⧺ gscope) scope random_oracle)
Proof
rpt strip_tac >>
fs[copyin_def] >>
assume_tac all_arg_update_imp >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
`ZIP ((MAP (λ(e,x,d). d) e_x_d_list),
 ZIP ((MAP (λ(e,x,d). x) e_x_d_list) ,
      (MAP (λ(e,x,d). e) e_x_d_list)))`,
 `scopest ⧺ gscope`, `scope`
])) >>
gvs[map_distrub, AllCaseEqs()] >> (
 metis_tac[]
)
QED






(**********************************************)
(* show implication copyin ==> well formed *)
(**********************************************)



val wf_arg_list_implied = prove (``

!dxel d (x:string) e ci_scope ss random_oracle tmp i'.
 ALL_DISTINCT (MAP (λ(d,x,e). x) dxel ⧺ [x]) /\
 check_args_red (MAP (λ(d,x,e). d) dxel ⧺ [d])
          (MAP (λ(d,x,e). e) dxel ⧺ [e]) /\
 SOME (ci_scope, i') = update_arg_for_newscope ss random_oracle (SOME tmp) (d,x,e) ==>
 wf_arg_list [d] [x] [e] ss
``,

rpt strip_tac >>
fs[wf_arg_list_def] >>
fs[wf_arg_def] >>
fs[update_arg_for_newscope_def] >>
fs[one_arg_val_for_newscope_def] >>
PairCases_on ‘tmp’ >>
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
rpt strip_tac >>
Cases_on `dxel = []` >| [
 gvs[]
 ,

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
rpt strip_tac >>
RES_TAC >>
PairCases_on `h` >>
fs[] >>
fs[check_args_red_def] >>
Cases_on `is_arg_red h0 h2` >> gvs[]
);




val update_new_scope_wf_args = prove ( ``
∀dxel ci_scope i' ss random_oracle i.
     ALL_DISTINCT (MAP (λ(d,x,e). x) dxel) /\
     check_args_red (MAP (λ(d,x,e). d) dxel)
          (MAP (λ(d,x,e). e) dxel) /\
     SOME (ci_scope, i') =
     FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) (dxel)
      ⇒
     wf_arg_list (MAP (λ(d,x,e). d) dxel)
                  (MAP (λ(d,x,e). x) dxel)
		  (MAP (λ(d,x,e). e) dxel) (ss) ``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC] >> (fs[SNOC_APPEND]) >- (
 fs[wf_arg_list_def]
) >>
PairCases_on `x` >>
fs[] >>
`ALL_DISTINCT (MAP (λ(d,x,e). x) dxel)` by fs[ALL_DISTINCT_APPEND] >>
`check_args_red (MAP (λ(d,x,e). d) dxel)
 (MAP (λ(d,x,e). e) dxel)` by IMP_RES_TAC check_args_red_normalize >>
fs[] >>
Cases_on `FOLDL (update_arg_for_newscope ss random_oracle) (SOME ([], i)) dxel` >| [
 fs[update_arg_for_newscope_def],

 PairCases_on `x` >>
 metis_tac[wf_arg_list_normalize_imp1, wf_arg_list_implied]
]
);





val all_update_new_scope_wf_args = prove ( ``
∀e_x_d_list ci_scope i' ss i random_oracle.
     ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) /\
     check_args_red (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) /\
     SOME (ci_scope, i') =
     all_arg_update_for_newscope (MAP (λ(e_,x_,d_). x_) e_x_d_list)
       (MAP (λ(e_,x_,d_). d_) e_x_d_list) (MAP (λ(e_,x_,d_). e_) e_x_d_list)
       (ss) i random_oracle ⇒
     wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
       (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
       (ss) ``,

rpt strip_tac >>
assume_tac update_new_scope_wf_args >>
fs[all_arg_update_for_newscope_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ZIP (MAP (λ(e_,x_,d_). d_) e_x_d_list,
    ZIP (MAP (λ(e_,x_,d_). x_) e_x_d_list,
         MAP (λ(e_,x_,d_). e_) e_x_d_list))`,
	 `ci_scope`, ‘i'’, `ss`, ‘random_oracle’, ‘i’])) >>
rfs[map_distrub]
);





val copyin_imp_wf_args2 = prove ( ``
! e_x_d_list ci_scope gscope scopest i random_oracle.
ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) /\
check_args_red (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) /\
SOME ci_scope =
        copyin (MAP (λ(e_,x_,d_). x_) e_x_d_list)
          (MAP (λ(e_,x_,d_). d_) e_x_d_list)
          (MAP (λ(e_,x_,d_). e_) e_x_d_list) gscope scopest i random_oracle ==>
( wf_arg_list
        (MAP (\(e,x,d).d) e_x_d_list)
	(MAP (\(e,x,d).x) e_x_d_list)
	(MAP (\(e,x,d).e) e_x_d_list) (scopest ++ gscope)) 
``,
fs[copyin_def] >>
rpt strip_tac >>
gvs[AllCaseEqs()] >>
irule all_update_new_scope_wf_args >>
gs[] >>
metis_tac[]
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
rpt strip_tac >>
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
rpt strip_tac >>
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
(*(type_of_v (v_err x) = t_tau tau_err) /\*)
(type_of_v (v_str x) = t_string_names_a [x] ) /\
(type_of_v (v_struct xvl) =
  t_tau (tau_xtl struct_ty_struct ( MAP (\xv . (FST xv ,  rm_t (type_of_v (SND xv))   )) xvl   ) ) ) /\
(type_of_v (v_header boolv xvl) =
  t_tau (tau_xtl struct_ty_header ( MAP (\xv . (FST xv ,  rm_t (type_of_v (SND xv))   )) xvl   ) ) )
`
(WF_REL_TAC `measure v_size` >>
 fs[v_size_def] >>
 rpt strip_tac >>
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
  !tau random_oracle i. v_typ v (t_tau tau) F ==> v_typ (FST $ init_out_v random_oracle i v) (t_tau tau) F
`;


val init_out_svl_typed_def = Define `
 init_out_svl_typed (svl: (string # v) list ) (ty:'a itself) =
   !(v:v). MEM v (SND (UNZIP svl)) ==> init_out_v_typed (v) (ty:'a itself)
`;

val init_out_sv_tup_typed_def = Define `
 init_out_sv_tup_typed  (tup : (string#v) ) (ty:'a itself) =
  init_out_v_typed ((SND tup)) (ty:'a itself)
`;


Theorem FOLDL_init_out_v_SNOC[local]:
!t t' random_oracle h' r.
FST
 (FOLDL
    (λ(l,i') (x,v,tau).
         (λ(v',i''). (v'::l,i''))
           (init_out_v random_oracle i' v)) (SNOC h' t',r) t) =
SNOC h' (FST
 (FOLDL
    (λ(l,i') (x,v,tau).
         (λ(v',i''). (v'::l,i''))
           (init_out_v random_oracle i' v)) (t',r) t))
Proof
Induct >> (
 rpt strip_tac >>
 gs[FOLDL]
) >>
PairCases_on ‘h’ >>
gvs[] >>
Cases_on ‘init_out_v random_oracle r h1’ >> gs[] >>
qpat_assum ‘!random_oracle h'. _’ (fn thm => REWRITE_TAC[GSYM thm]) >>
gs[]
QED

Theorem FOLDL_init_out_v_SNOC_tup[local]:
!t t' random_oracle h' r.
FST
 (FOLDL
    (λ(l,i') (x,v).
         (λ(v',i''). ((x:string,v')::l,i''))
           (init_out_v random_oracle i' v)) (SNOC h' t',r) t) =
SNOC h' (FST
 (FOLDL
    (λ(l,i') (x,v).
         (λ(v',i''). ((x,v')::l,i''))
           (init_out_v random_oracle i' v)) (t',r) t))
Proof
Induct >> (
 rpt strip_tac >>
 gs[FOLDL]
) >>
PairCases_on ‘h’ >>
gvs[] >>
Cases_on ‘init_out_v random_oracle r h1’ >> gs[] >>
qpat_assum ‘!random_oracle h'. _’ (fn thm => REWRITE_TAC[GSYM thm]) >>
gs[]
QED

Theorem FOLDL_init_out_v_SNOC_sing[local]:
!t t' random_oracle h' r.
FST
 (FOLDL
    (λ(l,i') (x,v).
         (λ(v',i''). (v'::l,i''))
           (init_out_v random_oracle i' v)) (SNOC h' t',r) t) =
SNOC h' (FST
 (FOLDL
    (λ(l,i') (x,v).
         (λ(v',i''). (v'::l,i''))
           (init_out_v random_oracle i' v)) (t',r) t))
Proof
Induct >> (
 rpt strip_tac >>
 gs[FOLDL]
) >>
PairCases_on ‘h’ >>
gvs[] >>
Cases_on ‘init_out_v random_oracle r h1’ >> gs[] >>
qpat_assum ‘!random_oracle h'. _’ (fn thm => REWRITE_TAC[GSYM thm]) >>
gs[]
QED

Theorem FOLDL_init_out_v_LENGTH[local]:
!t random_oracle q r xl vl r'.
 LENGTH $ FST $ FOLDL
  (λ(x_v_l,i') (x,v,tau).
       (λ(v,i''). (v::x_v_l,i''))
         (init_out_v random_oracle i' v)) ([],r) t = LENGTH t
Proof
Induct >> (
 gs[]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[] >>
Cases_on ‘init_out_v random_oracle r h1’ >>
gs[] >>
REWRITE_TAC[GSYM SNOC] >>
REWRITE_TAC[Once FOLDL_init_out_v_SNOC] >>
gs[LENGTH_SNOC]
QED

Theorem FOLDL_init_out_v_oracle_index[local]:
!t random_oracle i r.
 i < LENGTH t ==>
 ?j.
   EL i
     (REVERSE
        (FST
           (FOLDL
              (λ(l,i') (x,v,tau).
                   (λ(v',i''). (v'::l,i''))
                     (init_out_v random_oracle i' v)) ([],r) t))) =
   FST (init_out_v random_oracle j (EL i (MAP (FST o SND) t)))                     
Proof
Induct >> (
 gs[]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[] >>
Cases_on ‘init_out_v random_oracle r h1’ >>
gs[] >>
REWRITE_TAC[GSYM SNOC] >>
REWRITE_TAC[Once FOLDL_init_out_v_SNOC] >>
gs[REVERSE_SNOC] >>
Cases_on ‘i’ >- (
 gs[] >>
 qexists_tac ‘r’ >>
 gs[]
) >>
gs[]
QED

Theorem FOLDL_init_out_v_triple_equiv[local]:
!x_v_tau_list x_list v_list tau_list random_oracle i l'.
LENGTH v_list = LENGTH tau_list ==>
x_v_tau_list = ZIP(x_list, ZIP(v_list, tau_list)) ==>
FST
 (FOLDL
  (λ(x_v_l',i') (x,v,tau).
       (λ(v',i''). (v'::x_v_l',i''))
         (init_out_v random_oracle i' v)) (l',i) x_v_tau_list) = 
FST
 (FOLDL
  (λ(x_v_l',i') (x,v).
       (λ(v',i''). (v'::x_v_l',i''))
         (init_out_v random_oracle i' v)) (l',i) (ZIP(x_list,v_list)))
Proof
Induct_on ‘x_list’ >> (
 rpt strip_tac >>
 gs[ZIP_def]
) >>
Cases_on ‘v_list’ >> Cases_on ‘tau_list’ >> gs[ZIP_def] >>
res_tac >>
Cases_on ‘init_out_v random_oracle i h'’ >>
gs[]
QED

(* TODO: Rename *)
Theorem FOLDL_init_out_v_MAP_FST_imp[local]:
!x_v_list x_v_list' l random_oracle i i'.
 (FOLDL
  (λ(x_v_l',i') (x:string,v).
       (λ(v',i''). ((x,v')::x_v_l',i''))
         (init_out_v random_oracle i' v)) (l,i) x_v_list) = (x_v_list', i') ==> 
 (FOLDL
  (λ(x_v_l',i') (x,v).
       (λ(v',i''). (v'::x_v_l',i''))
         (init_out_v random_oracle i' v)) (MAP SND l,i) x_v_list) = (MAP SND x_v_list', i')
Proof
Induct >> (
 gs[]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[] >>
Cases_on ‘init_out_v random_oracle i h1’ >>
gs[] >>
res_tac >>
FULL_SIMP_TAC (srw_ss()) []
QED

Theorem FOLDL_init_out_v_identifiers[local]:
!l i random_oracle l' i'.
 FOLDL
          (λ(x_v_l',i') (x:string,v).
               (λ(v',i''). ((x,v')::x_v_l',i''))
                 (init_out_v random_oracle i' v)) ([],i)
          l =
   (l',i') ==>
MAP FST l = REVERSE $ MAP FST l'
Proof
Induct >> (
 gs[]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[] >>
Cases_on ‘init_out_v random_oracle i h1’ >>
gs[] >>
‘FST $ FOLDL
          (λ(x_v_l',i') (x,v).
               (λ(v',i''). ((x,v')::x_v_l',i''))
                 (init_out_v random_oracle i' v)) ([(h0,q)],r) l =
        l'’ by gs[] >>
FULL_SIMP_TAC bool_ss [GSYM SNOC] >>        
FULL_SIMP_TAC bool_ss [Once FOLDL_init_out_v_SNOC_tup] >>
Cases_on ‘FOLDL
                (λ(x_v_l',i') (x,v).
                     (λ(v',i''). ((x,v')::x_v_l',i''))
                       (init_out_v random_oracle i' v)) ([],r) l’ >>
res_tac >>
gvs[]
QED

Theorem MAP_FST_o_SND:
!l1 l2 l3.
LENGTH l1 = LENGTH l2 ==>
LENGTH l2 = LENGTH l3 ==>
MAP (FST ∘ SND) (ZIP (l1,ZIP (l2,l3))) = l2
Proof
Induct_on ‘l1’ >> (
 gs[]
) >>
rpt strip_tac >>
Cases_on ‘l2’ >> gs[] >>
Cases_on ‘l3’ >> gs[]
QED

val init_typed =
prove (``
(! (ty:'a itself).
(! v  . init_out_v_typed v ty) /\
(! svl. init_out_svl_typed svl ty) /\
(! sv . init_out_sv_tup_typed sv ty))``,

strip_tac >>
Induct >> (
 fs[init_out_v_typed_def] >> 
 rpt strip_tac >>
 fs[Once v_typ_cases] >>
 fs[init_out_v_typed_def, init_out_v_def]
) >- (
 (* v_bit *)
 rpt strip_tac >>
 PairCases_on `p` >>
 fs[bs_width_def, extend_def, init_out_v_def]
) >- (
 (* v_struct *)
 gvs[clause_name_def] >>
 qexists_tac ‘ZIP(MAP(λ(x,v,tau). x) (x_v_tau_list:(string#v#tau) list),
              ZIP (REVERSE $ FST (FOLDL (λ(l,i') (x:string,v,tau). (λ(v',i''). (v'::l,i''))
                       (init_out_v random_oracle i' v)) ([],i) x_v_tau_list) ,
                     MAP (λ(x,v,tau). tau) x_v_tau_list))’ >>
 gvs[] >>
 ‘?x_list v_list tau_list. x_v_tau_list = ZIP(x_list:string list,(ZIP(v_list,tau_list))) /\ LENGTH x_list = LENGTH v_list /\ LENGTH v_list = LENGTH tau_list’ by (
  qexistsl_tac [‘MAP (λx. FST x) x_v_tau_list’, ‘MAP (λx. FST (SND x)) x_v_tau_list’, ‘MAP (λx. SND (SND x)) x_v_tau_list’] >>
  simp[Once $ Q.ISPEC ‘x_v_tau_list:((string#v#tau) list)’ ZIP_tri_id1]
 ) >>
 ‘LENGTH (FST
   (FOLDL
      (λ(l,i') (x,v,tau).
           (λ(v',i''). (v'::l,i''))
             (init_out_v random_oracle i' v)) ([],i)
      (ZIP (x_list,ZIP (v_list,tau_list))))) = LENGTH tau_list’ by gs[FOLDL_init_out_v_LENGTH] >>
 gvs[map_distrub] >>
 ‘?v_list' i'. (FOLDL
              (λ(x_v_l',i') (x,v).
                   (λ(v',i''). ((x,v')::x_v_l',i''))
                     (init_out_v random_oracle i' v)) ([],i)
              (ZIP (x_list,v_list))) = (ZIP(REVERSE x_list, v_list'), i') /\ LENGTH v_list' = LENGTH x_list’ by (
  qexistsl_tac [‘MAP SND $ FST $ FOLDL
            (λ(x_v_l',i') (x,v).
                 (λ(v',i''). ((x,v')::x_v_l',i''))
                   (init_out_v random_oracle i' v)) ([],i)
            (ZIP (x_list,v_list))’, ‘SND $ FOLDL
            (λ(x_v_l',i') (x,v).
                 (λ(v',i''). ((x,v')::x_v_l',i''))
                   (init_out_v random_oracle i' v)) ([],i)
            (ZIP (x_list,v_list))’] >>
  Cases_on ‘FOLDL
             (λ(x_v_l',i') (x,v).
                  (λ(v',i''). ((x,v')::x_v_l',i''))
                    (init_out_v random_oracle i' v)) ([],i)
             (ZIP (x_list,v_list))’ >> gs[] >>
  strip_tac >- (
   ‘REVERSE x_list = MAP FST q’ suffices_by (
    strip_tac >>
    gvs[ZIP_MAP_FST_SND]
   ) >>
   imp_res_tac FOLDL_init_out_v_identifiers >>
   gs[MAP_ZIP]
  ) >>
  ‘?x_v_tau_list. x_v_tau_list = ZIP(x_list,(ZIP(v_list,tau_list)))’ by gs[] >>
  imp_res_tac FOLDL_init_out_v_triple_equiv >>
  gs[] >>
  imp_res_tac FOLDL_init_out_v_MAP_FST_imp >>
  gvs[]
 ) >>
 gs[REVERSE_ZIP] >>
 strip_tac >- (
  ‘v_list' = FST
              (FOLDL
                 (λ(l,i') (x,v,tau).
                      (λ(v',i''). (v'::l,i''))
                        (init_out_v random_oracle i' v)) ([],i)
                 (ZIP (x_list,ZIP (v_list,tau_list))))’ suffices_by gs[] >>
  ‘v_list' = MAP SND $ FST $ FOLDL
         (λ(x_v_l',i') (x,v).
              (λ(v',i''). ((x,v')::x_v_l',i''))
                (init_out_v random_oracle i' v)) ([],i)
         (ZIP (x_list,v_list))’ by gs[MAP_ZIP] >>
  gvs[] >>
  ‘?x_v_tau_list. x_v_tau_list = ZIP(x_list,(ZIP(v_list,tau_list)))’ by gs[] >>
  imp_res_tac FOLDL_init_out_v_triple_equiv >>
  gvs[] >>
  Cases_on ‘FOLDL
                (λ(x_v_l',i') (x,v).
                     (λ(v',i''). ((x,v')::x_v_l',i''))
                       (init_out_v random_oracle i' v)) ([],i)
                (ZIP (x_list,v_list))’ >> gs[] >>
  imp_res_tac FOLDL_init_out_v_MAP_FST_imp >>
  gvs[]
 ) >>
 rpt strip_tac >>
 gvs[init_out_svl_typed_def] >>
 subgoal ‘MEM (EL i'' v_list) v_list’ >- gvs[EL_MEM] >>
 gvs[init_out_v_typed_def] >>
 ‘i'' < LENGTH $ ZIP (x_list,ZIP (v_list,tau_list))’ by gs[] >>
 imp_res_tac FOLDL_init_out_v_oracle_index >>
 ‘MAP (FST ∘ SND) (ZIP (x_list,ZIP (v_list,tau_list))) = v_list’ by (
  metis_tac[MAP_FST_o_SND]
 ) >>
 metis_tac[]
) >- (
 (* v_header *)
 gvs[clause_name_def] >>
 qexistsl_tac [‘ZIP(MAP(λ(x,v,tau). x) (x_v_tau_list:(string#v#tau) list),
              ZIP (REVERSE $ FST (FOLDL (λ(l,i') (x:string,v,tau). (λ(v',i''). (v'::l,i''))
                       (init_out_v random_oracle i' v)) ([],i) x_v_tau_list) ,
                     MAP (λ(x,v,tau). tau) x_v_tau_list))’, ‘F’] >>
 gvs[] >>
 ‘?x_list v_list tau_list. x_v_tau_list = ZIP(x_list,(ZIP(v_list,tau_list))) /\ LENGTH x_list = LENGTH v_list /\ LENGTH v_list = LENGTH tau_list’ by (
  qexistsl_tac [‘MAP (λx. FST x) x_v_tau_list’, ‘MAP (λx. FST (SND x)) x_v_tau_list’, ‘MAP (λx. SND (SND x)) x_v_tau_list’] >>
  simp[Once $ Q.ISPEC ‘x_v_tau_list:((string#v#tau) list)’ ZIP_tri_id1]
 ) >>
 ‘LENGTH (FST
   (FOLDL
      (λ(l,i') (x,v,tau).
           (λ(v',i''). (v'::l,i''))
             (init_out_v random_oracle i' v)) ([],i)
      (ZIP (x_list,ZIP (v_list,tau_list))))) = LENGTH tau_list’ by gs[FOLDL_init_out_v_LENGTH] >>
 gvs[map_distrub] >>
 ‘?v_list' i'. (FOLDL
              (λ(x_v_l',i') (x,v).
                   (λ(v',i''). ((x,v')::x_v_l',i''))
                     (init_out_v random_oracle i' v)) ([],i)
              (ZIP (x_list,v_list))) = (ZIP(REVERSE x_list, v_list'), i') /\ LENGTH v_list' = LENGTH x_list’ by (
  qexistsl_tac [‘MAP SND $ FST $ FOLDL
            (λ(x_v_l',i') (x,v).
                 (λ(v',i''). ((x,v')::x_v_l',i''))
                   (init_out_v random_oracle i' v)) ([],i)
            (ZIP (x_list,v_list))’, ‘SND $ FOLDL
            (λ(x_v_l',i') (x,v).
                 (λ(v',i''). ((x,v')::x_v_l',i''))
                   (init_out_v random_oracle i' v)) ([],i)
            (ZIP (x_list,v_list))’] >>
  Cases_on ‘FOLDL
             (λ(x_v_l',i') (x,v).
                  (λ(v',i''). ((x,v')::x_v_l',i''))
                    (init_out_v random_oracle i' v)) ([],i)
             (ZIP (x_list,v_list))’ >> gs[] >>
  strip_tac >- (
   ‘REVERSE x_list = MAP FST q’ suffices_by (
    strip_tac >>
    gvs[ZIP_MAP_FST_SND]
   ) >>
   imp_res_tac FOLDL_init_out_v_identifiers >>
   gs[MAP_ZIP]
  ) >>
  ‘?x_v_tau_list. x_v_tau_list = ZIP(x_list,(ZIP(v_list,tau_list)))’ by gs[] >>
  imp_res_tac FOLDL_init_out_v_triple_equiv >>
  gs[] >>
  imp_res_tac FOLDL_init_out_v_MAP_FST_imp >>
  gvs[]
 ) >>  
 gs[REVERSE_ZIP] >>
 strip_tac >- (
  ‘v_list' = FST
              (FOLDL
                 (λ(l,i') (x,v,tau).
                      (λ(v',i''). (v'::l,i''))
                        (init_out_v random_oracle i' v)) ([],i)
                 (ZIP (x_list,ZIP (v_list,tau_list))))’ suffices_by gs[] >>
  ‘v_list' = MAP SND $ FST $ FOLDL
         (λ(x_v_l',i') (x,v).
              (λ(v',i''). ((x,v')::x_v_l',i''))
                (init_out_v random_oracle i' v)) ([],i)
         (ZIP (x_list,v_list))’ by gs[MAP_ZIP] >>
  gvs[] >>
  ‘?x_v_tau_list. x_v_tau_list = ZIP(x_list,(ZIP(v_list,tau_list)))’ by gs[] >>
  imp_res_tac FOLDL_init_out_v_triple_equiv >>
  gvs[] >>
  Cases_on ‘FOLDL
                (λ(x_v_l',i') (x,v).
                     (λ(v',i''). ((x,v')::x_v_l',i''))
                       (init_out_v random_oracle i' v)) ([],i)
                (ZIP (x_list,v_list))’ >> gs[] >>
  imp_res_tac FOLDL_init_out_v_MAP_FST_imp >>
  gvs[]
 ) >>
 rpt strip_tac >- (
  simp[Once v_typ_cases, clause_name_def]
 ) >>
 gvs[init_out_svl_typed_def] >>
 subgoal ‘MEM (EL i'' v_list) v_list’ >- gvs[EL_MEM] >>
 gvs[init_out_v_typed_def] >>
 ‘i'' < LENGTH $ ZIP (x_list,ZIP (v_list,tau_list))’ by gs[] >>
 imp_res_tac FOLDL_init_out_v_oracle_index >>
 ‘MAP (FST ∘ SND) (ZIP (x_list,ZIP (v_list,tau_list))) = v_list’ by metis_tac[MAP_FST_o_SND] >>
 metis_tac[]
) >- (
 (* empty list *)
 gs[init_out_svl_typed_def]
) >- (
 (* list *)
 fs[init_out_svl_typed_def, init_out_sv_tup_typed_def] >>
 rpt strip_tac >> gvs[]
) >- (
 (* Tuple *)
 fs[init_out_sv_tup_typed_def] >>
 fs[init_out_v_typed_def] >>
 gvs[] >>
 Cases_on `v` >- (
  Cases_on `tau` >> fs[Once v_typ_cases] >>
  fs[Once v_typ_cases]
 ) >- (
  Cases_on `tau` >> fs[Once v_typ_cases] >>
  fs[Once v_typ_cases]
 ) >- (
  Cases_on `tau` >> fs[Once v_typ_cases] >>
  fs[Once v_typ_cases]
 ) >- (
  fs[clause_name_def] >>
  rpt strip_tac >>
  OPEN_V_TYP_TAC ``v_struct l`` >>
  metis_tac[]
 ) >- (
  fs[clause_name_def] >>
  rpt strip_tac >>
  OPEN_V_TYP_TAC ``v_struct l`` >>
  metis_tac[]
 ) >- (
  Cases_on `tau` >> fs[Once v_typ_cases] >>
  fs[Once v_typ_cases]
 ) >>
 Cases_on `tau` >> fs[Once v_typ_cases] >>
 fs[Once v_typ_cases]
)
);



Theorem FIND_in_conc:
! xtl s a . 
FIND (λx. FST x = s) xtl = SOME a ==>
     (FST a=s)
Proof     

Induct_on `xtl` >>
rpt strip_tac >>
fs[FIND_def, INDEX_FIND_def] >>
Cases_on ` FST h = s` >> gvs[] >>
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#'b)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`, `xtl`, `(λx. FST x = s)`, `z`])) >>
   gvs[GSYM ADD1] >> 
RES_TAC
QED



Theorem ev_not_typed_T:
! t_g t_sl T_e v tau .
   ~ e_typ (t_g,t_sl) T_e (e_v v) (t_tau tau) T
Proof   
fs[Once e_typ_cases] >>
fs[Once v_typ_cases] >>
gvs[]
QED



Theorem lookup_lval_exists:
! ss v x s .
lookup_lval (ss) (lval_field x s) = SOME v ==>
? v' . lookup_lval (ss) x = SOME v' 
Proof

rpt strip_tac >>
fs[lookup_lval_def] >>
Cases_on `lookup_lval ss x` >>
fs[] 
QED



Theorem acc_struct_val_typed:
! v strct s struct_ty x_tau_list tau .
acc_f strct s = SOME v /\
v_typ strct (t_tau (tau_xtl struct_ty x_tau_list)) F /\
correct_field_type x_tau_list s tau ==>
  v_typ v (t_tau tau) F
Proof

rpt strip_tac >>
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
  ( 
  `EL q (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) = (x0',v)` by fsrw_tac [] [INDEX_FIND_EQ_SOME_0] >>
   IMP_RES_TAC EL_simp5 >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`v`, `x0'`])) >> rfs[]
 )) >>
gvs[]
QED





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
rpt strip_tac >>
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
  subgoal `similarl (λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2) (scopest ++ gscope) (t_sl ++ t_g) ` >-
  (fs[similarl_def] >>
  IMP_RES_TAC LIST_REL_APPEND) >>

  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                         ``:'b`` |-> ``:(tau#lval option )``] R_lookup_map_scopesl)  >>
			 
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)`,
   `x'`,
   `(varn_name s)`,
   `x`,
   `(t_sl ⧺ t_g)`,
   `(scopest ⧺ gscope)`])) >>
   PairCases_on `x` >>
   PairCases_on `x'` >>
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
                         ``:'b`` |-> ``:(tau#lval option)``] R_lookup_map_scopesl)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)`,
    `x'`,
    `(varn_star f)`,
    `(v',x1)`,
    `(t_g)`,
    `(gscope)`])) >>
   PairCases_on `x'` >>
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

 IMP_RES_TAC lookup_lval_exists  >>
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
! e gscope t_g scopest t_sl x d tau T_e scope' b t random_oracle.
type_scopes_list gscope t_g /\
type_scopes_list scopest t_sl /\
star_not_in_sl scopest /\
( e_typ (t_g,t_sl) T_e e (t_tau tau) b) /\
wf_arg d x e (scopest ⧺ gscope) /\
copyin_abstract [x] [d] [e] (scopest ⧺ gscope) scope' random_oracle ==>
type_scopes_list [scope'] [ZIP ((mk_varn [x]), ZIP([tau], [get_lval_of_e e] ))]
``,

fs[type_scopes_list_def] >>
fs[mk_varn_def] >>
rpt strip_tac >>
Cases_on `is_d_out d` >>

SIMP_TAC list_ss [similarl_def, similar_def] >>
fs[mk_varn_def] >>
fs[copyin_abstract_def] >>
qpat_x_assum ‘!oracle_index. _’ (fn thm => assume_tac $ Q.SPECL [‘oracle_index'’] thm) >> fs[] >>

Cases_on `one_arg_val_for_newscope d e (scopest ⧺ gscope) oracle_index' random_oracle` >> (fs[]) >>
PairCases_on `x'` >>
qexists_tac `(varn_name x,x'0,x'2)` >>
gvs[] >| [
 (** inout & out directed **)
 subgoal `scope' = [(varn_name x,x'0,x'2)]` >- (
  Induct_on `scope'` >>
  fs[]
 ) >>
 fs[] >> rw[] >> (
  fs[wf_arg_def, is_d_out_def] >>
  fs[one_arg_val_for_newscope_def, is_d_out_def] >> gvs[] >>
  Cases_on `is_d_in d` >> fs[] >> gvs[]
 ) >- (
   (* inout *)
   ASSUME_TAC out_dir_lookup_typed >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`e`,`tau`,  `lval`, `T_e`, `gscope`, `t_g`,
   `scopest`, `t_sl`, `b`, `d`, `x`])) >>
   gvs[type_scopes_list_def] >> 
   fs[wf_arg_def] >> gvs[] >>
   metis_tac[]
 ) >>
   ASSUME_TAC out_dir_lookup_typed >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`e`,`tau`,  `lval`, `T_e`, `gscope`, `t_g`,
   `scopest`, `t_sl`, `b`, `d`, `x`])) >>
   gvs[type_scopes_list_def] >> 
   fs[wf_arg_def] >> gvs[] >>
   ‘v_typ v (t_tau tau) F’ by (
    metis_tac[]
   ) >>
   (* out *)
   ASSUME_TAC init_typed >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
   fs[] >>
   fs[init_out_v_typed_def] >>
   gvs[] >>
   res_tac >>
   ‘x'0 = FST $ init_out_v random_oracle oracle_index' v’ suffices_by (
    rpt strip_tac >>
    FULL_SIMP_TAC bool_ss []
   ) >>
   rfs[],

  subgoal `scope' = [(varn_name x,x'0,x'2)]` >- (
   Induct_on `scope'` >>
   fs[]
  ) >>
  fs[] >> rw[] >>

  fs[one_arg_val_for_newscope_def] >>

  Cases_on `is_d_out d` >> fs[] >>

  Cases_on `v_of_e e` >> fs[] >> rw[] >>
  Cases_on `e` >> fs[is_const_def, v_of_e_def] >>
  rw[] >>

  Cases_on `b` >>
  IMP_RES_TAC ev_not_typed_T >>
  IMP_RES_TAC ev_types_v >>
  gvs[get_lval_of_e_def]
]
);


val similar_normalize = prove ( ``
∀l vl tl t v R a.
       LENGTH vl = LENGTH tl ∧ similar R [a] (ZIP ([v],[t])) ∧
       similar R l (ZIP (vl,tl)) ⇒
       similar R (a::l) (ZIP (v::vl,t::tl))``,

rpt strip_tac >>
fs[similar_def]
);












        

val CI_scope_list_typed = prove (``
! e_x_d_list scopest t_sl gscope t_g scope' e_tau_x_d_b_list T_e i random_oracle.
(LENGTH e_tau_x_d_b_list = LENGTH e_x_d_list) /\
type_scopes_list gscope t_g /\
type_scopes_list scopest t_sl /\
star_not_in_sl scopest /\
(∀i. i < LENGTH e_tau_x_d_b_list ⇒
            e_typ (t_g,t_sl)
              (T_e)
              (EL i (MAP (λ(e_,x_,d_). e_) e_x_d_list))
              (t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)))
              (EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list))) /\
wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list) 
            (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
            (scopest ⧺ gscope) /\
copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
          (MAP (λ(e,x,d). d) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope) scope' random_oracle ==>
type_scopes_list [scope']
          [ZIP
               (mk_varn (MAP (λ(e_,x_,d_). x_) e_x_d_list),
                ZIP
                  (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list,
                        MAP (λ(e_,x_,d_). get_lval_of_e e_) e_x_d_list))] ``,

Induct >| [

 rpt strip_tac >> fs[] >>
 fs[similar_def, copyin_abstract_def] >>
 SIMP_TAC list_ss [type_scopes_list_def, mk_varn_def] >>
 fs[similarl_def, similar_def] 
 ,

 rpt strip_tac >> fs[] >>
 PairCases_on `h` >> fs[] >>

 (* first show that the head is well typed*)
 subgoal `type_scopes_list [[HD scope']]
          [ZIP (mk_varn [h1], ZIP(  [HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)], [ get_lval_of_e h0]  ))] ` >- (	  
   `wf_arg h2 h1 h0 (scopest ⧺ gscope)` by IMP_RES_TAC wf_arg_normalization >>
   subgoal `copyin_abstract [h1] [h2] [h0] (scopest ⧺ gscope) [HD scope'] random_oracle` >-
     (IMP_RES_TAC copyin_abstract_normalize_tmp >>
      rfs[] ) >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>

  gvs[] >>
  ASSUME_TAC CI_scope_WT_single >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`h0`, `gscope`, `t_g`, `scopest`, `t_sl`, `h1`, `h2`,
  `(HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (α # tau # β # γ # bool) list)))`,
  `T_e`, `[HD scope']`,
  `(HD (MAP (λ(e_,tau_,x_,d_,b_). b_) (e_tau_x_d_b_list : (α # tau # β # γ # bool) list)))`])) >>
  gvs[] >>
  metis_tac[]
 ) >>


 (* now use the IH to show that the TL of the CI scope is also well type *)

 `wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
          (MAP (λ(e,x,d). x) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope)` by IMP_RES_TAC wf_arg_normalization >>
	  
 `copyin_abstract (MAP (λ(e,x,d). x) e_x_d_list)
          (MAP (λ(e,x,d). d) e_x_d_list) (MAP (λ(e,x,d). e) e_x_d_list)
          (scopest ⧺ gscope) (TL scope') random_oracle` by (IMP_RES_TAC copyin_abstract_normalize_tmp >>
                                              rfs[] ) >>
			      
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`scopest`,`t_sl`, `gscope`,`t_g`, `TL scope'`, `TL e_tau_x_d_b_list`, `T_e`, ‘random_oracle’ ])) >>
   subgoal `LENGTH (TL e_tau_x_d_b_list) = LENGTH e_x_d_list` >-
     (Cases_on `e_tau_x_d_b_list` >>
      Cases_on `e_x_d_list` >>
      fs[] ) >>
   gvs[] >>


  subgoal `(∀i. i < LENGTH e_x_d_list ⇒
             e_typ (t_g,t_sl) T_e
	                  (EL i (MAP (λ(e_,x_,d_). e_) e_x_d_list))
               (t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) (TL e_tau_x_d_b_list))))
                          (EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) (TL e_tau_x_d_b_list))))` >-
    ( rpt strip_tac >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i + 1` ])) >>
      gvs[ADD1] >>
      fs[EL_CONS] >>
      fs[PRE_SUB1] >>

      fs[Once EL_compute] >>
      Cases_on `i=0` >> gvs[] >| [
        Induct_on `e_tau_x_d_b_list` >> fs[]
        ,
        gvs[numeral_pre, PRE_SUB1,PRE_SUC_EQ] >>
        `LENGTH e_tau_x_d_b_list > 0 ` by fs[] >>

      subgoal `(EL (i + 1) (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)) =
               (EL i   (MAP (λ(e_,tau_,x_,d_,b_). tau_) (TL e_tau_x_d_b_list))) ` >-
        ( `EL (SUC i) (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list) =
           EL i (TL (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list)))` by gvs[EL] >>
           fs[ADD1] >>
           fs[EL, MAP_TL] ) >>

      subgoal `(EL (i + 1) (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list)) =
               (EL   i (MAP (λ(e_,tau_,x_,d_,b_). b_) (TL e_tau_x_d_b_list))) ` >-
        ( `EL (SUC i) (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list) =
           EL   i (TL (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list))` by gvs[EL] >>
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
   		                  ``:γ`` |-> ``:(tau # lval option)``] similar_normalize)  >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`TL (scope')`,
  ` (mk_varn (MAP (λ(e_,x_,d_). x_) (e_x_d_list : (e # string # d) list)))`,
  `ZIP (MAP (λ(e_,tau_,x_,d_,b_). tau_) (TL (e_tau_x_d_b_list : (α # tau # β # γ # bool) list)),
        MAP (λ(e_,x_,d_). get_lval_of_e e_) ( (e_x_d_list : (e # string # d) list)))`,
  `(HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (α # tau # β # γ # bool) list)), get_lval_of_e h0)`,
  `varn_name h1`,
  `(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)`,
  `HD scope'`
 ])) >>


 gvs[] >>
 fs[mk_varn_def] >>
 gvs[] >>


 subgoal `(HD scope'::TL scope' ) = scope'` >-
 (IMP_RES_TAC args_ci_scope_LENGTH2 >> gvs[] >>
  `LENGTH scope' > 0` by fs[] >>
  fs[NOT_NIL_EQ_LENGTH_NOT_0]) >>


 gvs[] >>
 fs[EL, MAP_TL] >> 

 fs[similar_def] >> gvs[] >>
 PairCases_on `x` >>
 gvs[] >>


 Q.EXISTS_TAC `(varn_name h1,  (HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)) , get_lval_of_e h0 )` >>
 Q.EXISTS_TAC `(ZIP (MAP (λx. varn_name x) (MAP (λ(e_,x_,d_). x_) e_x_d_list),
                     ZIP (TL (MAP (λ(e_,tau_,x_,d_,b_). tau_) ( e_tau_x_d_b_list) ) ,
                              MAP (λ(e_,x_,d_). get_lval_of_e e_) e_x_d_list
                         )))` >>
	  gvs[] >>
	  rw[] >>
	  rfs[] >>    

 fs[ZIP_def, ZIP] >>
 (*should be simple now to prove*)


   subgoal `(HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)::
             TL (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list) ) =
             (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list)` >-
  (`LENGTH e_tau_x_d_b_list > 0` by fs[] >> 
   fs[NOT_NIL_EQ_LENGTH_NOT_0]) >>


  ‘∀ (l1:varn list) (l2: tau list) (l3: lval option list) x1 x2 x3 .
   ZIP (x1::l1,ZIP(x2::l2,x3::l3)) = (x1,x2,x3):: ZIP(l1,ZIP(l2,l3)) ’ by gvs[ZIP_def] >>

 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [
   `MAP (λx. varn_name x) (MAP (λ(e_,x_,d_). x_) (e_x_d_list : (e # string # d) list))`,
   `TL (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (α # tau # β # γ # bool) list))`,
   ‘MAP (λ(e_,x_,d_). get_lval_of_e e_) (e_x_d_list : (e # string # d) list)’,
   ‘varn_name h1’, ‘HD (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (α # tau # β # γ # bool) list))’ ,
   ‘get_lval_of_e h0’           
  ])) >>
   METIS_TAC[]
]
);

        



Theorem LENGTH_imp_NULL:
 ∀ l1 l2 .          
LENGTH l1 = LENGTH l2 ⇒
(¬NULL l1 = ¬NULL l2)
Proof
Induct >> Induct_on ‘l2’ >> gvs[NULL]
QED



Theorem type_scopes_list_normalize:        
∀ sl tsl h h'.
  type_scopes_list (h::sl) (h'::tsl) <=>
  type_scopes_list [h] [h'] ∧                
  type_scopes_list (sl) (tsl)
Proof
gvs[type_scopes_list_def] >>
gvs[similarl_def]
QED

        
Theorem type_scopes_list_normalize2:        
  ∀ sl tsl h h'.
  LENGTH sl > 0 ∧  
  type_scopes_list (sl) (tsl) ==>
  type_scopes_list [HD sl] [HD tsl] ∧                
  type_scopes_list (TL sl) (TL tsl)
Proof

Induct >>
rpt strip_tac >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[] >>      
        
(subgoal ‘¬NULL tsl’ >-
   (IMP_RES_TAC type_scopes_list_LENGTH >>
    IMP_RES_TAC LENGTH_imp_NULL >>
    gvs[LENGTH_NOT_NULL] ))>>
     
‘(HD tsl)::(TL tsl) = tsl’ by METIS_TAC[CONS] >>
‘type_scopes_list (h::sl) (HD tsl::TL tsl)’ by fs[] >>

fs[Once type_scopes_list_normalize]   
QED    


Theorem type_scopes_list_EL:
∀ gscope tslg i .
type_scopes_list gscope tslg ⇒
( i < LENGTH tslg ⇒ type_scopes_list [EL i gscope] [EL i tslg])
Proof
Induct_on ‘gscope’ >>
Induct_on ‘tslg’ >>
Induct_on ‘i’ >>  
rpt strip_tac >>
gvs[] >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[] >>
IMP_RES_TAC type_scopes_list_normalize >> gvs[]      
QED


        
Theorem scopes_to_pass_typed_lem:
∀ gscope tslg funn func_map b_func_map delta_g delta_b g_scope_passed tslg_passed.
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ∧                                                                                                    
  scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ∧
  t_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed  ⇒
                type_scopes_list g_scope_passed tslg_passed                                                
Proof
gvs[scopes_to_pass_def, t_scopes_to_pass_def] >>
rpt strip_tac >>

Cases_on ‘funn’ >> gvs[] >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>

                                        
simp_tac list_ss [Once type_scopes_list_normalize] >>
srw_tac [][type_scopes_list_EL] >>
simp_tac list_ss [type_scopes_list_def, similarl_def, similar_def]
QED




Theorem scopes_to_pass_typed_thm:
  ∀ gscope tslg funn func_map b_func_map delta_g delta_b g_scope_passed tslg_passed
  apply_table_f (ext_map: 'a ext_map) pars_map tbl_map order t_scope_list_g delta_x delta_t Prs_n.
  WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
       order tslg delta_g delta_b delta_x delta_t Prs_n ∧
       type_scopes_list gscope tslg ∧                 
  scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ∧
  t_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed  ⇒
                type_scopes_list g_scope_passed tslg_passed                                                
Proof
  gvs[WT_c_cases] >>
  rpt strip_tac >>
  drule scopes_to_pass_typed_lem >>
  rpt strip_tac >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope’,‘tslg’,‘funn’, ‘func_map’, ‘delta_g’, ‘g_scope_passed’, ‘tslg_passed’])) >>
  gvs[]         
QED




val lookup_parse_err_in_xdl = prove (“
∀ xdl tl.
EVERY (λ(x,d). x ≠ "parseError") (MAP (λ(x_,d_). (x_,d_)) xdl) ⇒
ALOOKUP (ZIP (mk_varn (MAP (λ(x_,d_). x_) xdl),tl))  (varn_name "parseError") = NONE ”,

Induct_on ‘xdl’ >>
Induct_on ‘tl’ >>
rpt strip_tac >>
gvs[mk_varn_def, ZIP_def]>>
PairCases_on ‘h'’ >>
gvs[]
);



        
val lookup_map_parse_err_in_xdl = prove ( “
∀ xdl tl.        
not_parseError_str (xdl) ⇒        
lookup_map [ZIP (mk_varn (MAP FST xdl), tl)] (varn_name "parseError") = NONE ”,

gvs[not_parseError_str_def, lookup_map_def] >>
gvs[topmost_map_def, find_topmost_map_def] >>

rpt strip_tac >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[INDEX_FIND_EQ_SOME_0] >>
      
ASSUME_TAC lookup_parse_err_in_xdl >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘xdl’,‘tl’])) >>
gvs[ELIM_UNCURRY] >>
gvs[map_fst_EQ]
);


Theorem MAP_FST_3_2:
∀l .
  MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) l) = MAP  (λ(e_,x_,d_). (x_)) l ∧
  MAP SND (MAP (λ(e_,x_,d_). (x_,d_)) l) = MAP  (λ(e_,x_,d_). (d_)) l
Proof  
Induct >> gvs[] >>
rpt strip_tac >> PairCases_on ‘h’ >> gvs[]
QED


        
     
Theorem MAP_MAP_txd:
∀l.
MAP (λ(t,x,d). t) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) l) =
MAP (λ(e_,tau_,x_,d_,b_). (tau_)) l  ∧
MAP (λ(t,x,d). x) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) l) =
MAP (λ(e_,tau_,x_,d_,b_). (x_)) l ∧
MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) l) =
MAP (λ(e_,tau_,x_,d_,b_). (d_)) l ∧
MAP FST          (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) l) =
MAP (λ(e_,tau_,x_,d_,b_). (tau_)) l
Proof
Induct >> gvs[] >>
rpt strip_tac >> PairCases_on ‘h’ >> gvs[]
QED


Theorem MAP_SND_4_2:
∀ l . MAP (λ(e_,e'_,x_,d_). d_) l = MAP SND (MAP (λ(e_,e'_,x_,d_). (x_,d_)) l)
Proof
Induct_on ‘l’ >> gvs[] >> rpt strip_tac >> PairCases_on ‘h’ >> gvs[]
QED






        

Theorem out_is_lval_normalisation:
! dl bl d b .
out_is_lval (d::dl) (b::bl) <=>
(out_is_lval (dl) (bl) /\ (is_d_out (d) ⇒ b))
Proof

gvs[out_is_lval_def] >>
rpt strip_tac >>
EQ_TAC >>
rpt strip_tac >| [
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
]
QED                   

                                        

val wf_arg_imp_lval_consistent_single = prove (“
 ∀ d x e b ss.
wf_arg d x e ss ∧
(is_d_out d ⇒ b) ⇒
out_lval_consistent [get_lval_of_e e] [d]”,
gvs[out_lval_consistent_def, wf_arg_def ] >>
rpt strip_tac >>
Cases_on ‘is_d_out d’ >> gvs[] >>
Cases_on ‘e’ >>
gvs[get_lval_of_e_def, v_of_e_def]
);


        
Theorem wf_arg_imp_lval_consistent_single:
∀ e_x_d_list bl ss .
    LENGTH bl = LENGTH e_x_d_list ∧
wf_arg_list (MAP (λ(e,x,d). d) e_x_d_list)
            (MAP (λ(e,x,d). x) e_x_d_list)
            (MAP (λ(e,x,d). e) e_x_d_list)
            (ss) ∧
out_is_lval (MAP (λ(e_,x_,d_). d_) e_x_d_list) (bl) ⇒
out_lval_consistent (MAP (λ(e_,x_,d_). get_lval_of_e e_) e_x_d_list) (MAP (λ(e_,x_,d_). d_) e_x_d_list)
Proof
Induct >>                        
rpt strip_tac >| [
gvs[out_lval_consistent_def]
,
PairCases_on ‘h’ >> gvs[] >>
IMP_RES_TAC wf_arg_normalization >>
Cases_on ‘bl’ >> gvs[] >>
IMP_RES_TAC out_is_lval_normalisation >>
IMP_RES_TAC wf_arg_imp_lval_consistent_single >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’, ‘ss’])) >>
gvs[out_lval_consistent_def]
]
QED




                                        

(* the otherside of the implications hold at lval_typ_imp_e_typ *)

val e_typ_imp_lval_typ = prove (“ 
∀ e l tau t b T_e gtsl tsl. 
e_typ (gtsl,tsl) T_e e (t_tau t) T ∧
get_lval_of_e e = SOME l ⇒
lval_typ (gtsl,tsl) T_e l (t_tau t)”,

Induct >>                       
REPEAT GEN_TAC >> STRIP_TAC >>
gvs[get_lval_of_e_def, is_e_lval_def] >| [
    
 gvs[Once lval_typ_cases, clause_name_def] 
 ,
 BasicProvers.FULL_CASE_TAC >> gvs[] >>
 SIMP_TAC list_ss [Once lval_typ_cases] >>
 gvs[clause_name_def] >>                    
 Q.PAT_X_ASSUM `e_typ (gtsl,tsl) T_e (e_acc e s) (t_tau t) T`
   ( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [Once e_typ_cases] ) >>
 gvs[] >>
  METIS_TAC[]                        
 ,

 BasicProvers.FULL_CASE_TAC >> gvs[] >>
 SIMP_TAC list_ss [Once lval_typ_cases] >>
 gvs[clause_name_def] >>
                      
 Q.PAT_X_ASSUM `e_typ (gtsl,tsl) T_e (e_slice e e' e'') (t_tau t) T`
   ( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [Once e_typ_cases] ) >>
 gvs[] >>
  METIS_TAC[]    
  ]
);







val  wf_arg_imp_lval_typ = prove (“
∀ d b x e ss tslg tsl T_e tau lop.
(is_d_out d ⇒ b) ∧
wf_arg d x e ss ∧
e_typ (tslg,tsl) T_e e (t_tau tau) b ∧
get_lval_of_e e = SOME lop ⇒
lval_typ (tslg,tsl) T_e lop (t_tau tau) ”,

rpt strip_tac >>
gvs[wf_arg_def] >>
Cases_on ‘is_d_out d’ >> gvs[] >>              
IMP_RES_TAC e_typ_imp_lval_typ>>
gvs[] >>
Cases_on ‘e’ >> gvs[v_of_e_def, get_lval_of_e_def]                        
);

        
val  wf_arg_imp_lval_typ_sinlge = prove (“
∀ d b x e ss tslg tsl T_e tau lop t a.
out_is_lval [d] [b] ∧
wf_arg d x e ss ∧
e_typ (tslg,tsl) T_e e (t_tau tau) b ∧
ALOOKUP [(x,tau,get_lval_of_e e)] a = SOME (t, SOME lop) ⇒
lval_typ (tslg,tsl) T_e lop (t_tau t) ”,

rpt strip_tac >>
Cases_on ‘a=x’ >> gvs[] >>
gvs[out_is_lval_def, wf_arg_def] >>
Cases_on ‘is_d_out d’ >> gvs[] >>              
IMP_RES_TAC e_typ_imp_lval_typ>>
gvs[] >>
Cases_on ‘e’ >> gvs[v_of_e_def, get_lval_of_e_def]
);

                                       


        



val wf_arg_imp_lval_typ_sinlge_list = prove (“
∀ exdl tbl t lop T_e tslg tsl ss x.
LENGTH exdl = LENGTH tbl ∧
out_is_lval (MAP (λ(e,x,d). d) exdl) (MAP (λ(t,b). b) tbl) ∧
wf_arg_list (MAP (λ(e,x,d). d) exdl) (MAP (λ(e,x,d). x) exdl) (MAP (λ(e,x,d). e) exdl) (ss) ∧
(∀i. i < LENGTH tbl ⇒
            e_typ (tslg,tsl) T_e
                     (EL i (MAP (λ(e,x,d). e) exdl))
              (t_tau (EL i (MAP (λ(t,b). t) tbl)))
                     (EL i (MAP (λ(t,b). b) tbl)))  ∧

ALOOKUP (ZIP (mk_varn (MAP (λ(e,x,d). x) exdl),
              ZIP (MAP (λ(t,b). t) tbl, MAP (λ(e,x,d). get_lval_of_e e) exdl))) x = SOME (t,SOME lop) ⇒
lval_typ (tslg,tsl) T_e  lop (t_tau t) ”,

Induct >>
Cases_on ‘tbl’ >> gvs[] >>
rpt strip_tac >-
 gvs[mk_varn_def] >>
        
 PairCases_on ‘h'’ >> PairCases_on ‘h’ >> gvs[] >>
 IMP_RES_TAC wf_arg_normalization >>
 IMP_RES_TAC out_is_lval_normalisation >>             
 gvs[ALOOKUP_def, mk_varn_lemma2] >>
 Cases_on ‘varn_name h'1 = x’ >> gvs[] >| [

     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[] >>
     IMP_RES_TAC wf_arg_imp_lval_typ 
     ,
     LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’, ‘t'’,‘lop’,‘T_e’, ‘tslg’,‘tsl’, ‘ss’, ‘x’])) >>
     gvs[] >>
     subgoal ‘(∀i. i < LENGTH t ⇒
             e_typ (tslg,tsl) T_e (EL i (MAP (λ(e,x,d). e) exdl))
                   (t_tau (EL i (MAP (λ(t,b). t) t))) (EL i (MAP (λ(t,b). b) t)))’ >- (
       rpt strip_tac >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i+1’])) >>
       gvs[ADD1, EL_CONS] >> gvs[PRE_SUB1] 
       ) >> gvs[]
]
);




Theorem bv_casting_length1:
∀ n' v n.  n' = bs_width (bitv_cast n' (v,n))
Proof               
gvs[bitv_cast_def, bs_width_def, fixwidth_def, DROP]
QED

Theorem bv_casting_length2:
∀ n' bitv.  n' = bs_width (bitv_cast n' bitv)
Proof               
rpt strip_tac >> Cases_on ‘bitv’ >>
gvs[bitv_cast_def, bs_width_def, fixwidth_def, DROP]
QED

Theorem bool_casting_length:        
∀ n b'. n = bs_width (bool_cast n b')
Proof
gvs[bool_cast_def, bs_width_def, fixwidth_def, DROP]
QED




Theorem e_sem_struct:
!e apply_table_f ext_map func_map b_func_map pars_map tbl_map gscope scopest e' framel.
is_struct e ==>
e_red (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
      gscope scopest e e' framel ==>
is_struct e'
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 gs[is_struct_def]
) >| [
 Cases_on ‘v’ >> (
  gs[]
 ),

 ALL_TAC
] >> (
 Cases_on ‘e'’ >> (
  gs[]
 ) >- (
  Cases_on ‘v’ >> (
   gs[]
  ) >> (
   gvs[Once e_sem_cases]
  )
 ) >> (
  gvs[Once e_sem_cases]
 )
)
QED




(****************)
(****************)
(*  E SR        *)
(****************)
(****************)

Theorem SR_e:
!(ty:'a itself) .
(!e. sr_exp e ty) /\
(! (l1: e list). sr_exp_list l1 ty) /\
(! (l2: (string#e) list) .  sr_strexp_list l2 ty) /\
(! tup. sr_strexp_tup tup ty)
Proof

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
rpt strip_tac >>


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


 IMP_RES_TAC varn_is_typed >>  gvs[]
] 

,

(*****************)
(*expression list*)
(*****************)

fs[sr_exp_list_def] >>
rfs[sr_exp_def] >>
rpt strip_tac >>
FULL_SIMP_TAC (srw_ss()) [Once e_sem_cases]

,

(*****************)
(* field access  *)
(*****************)

SIMP_TAC list_ss [sr_exp_def] >>
rpt strip_tac >>
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

rpt strip_tac >>
SIMP_TAC std_ss [sr_exp_def] >>
rpt strip_tac >| [
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
(*  Cast        *)
(****************) 
rpt strip_tac  >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
rpt strip_tac >| [
    
    gvs[Once e_sem_cases] >| [
    OPEN_EXP_TYP_TAC ``(e_cast c e)`` >>
    gvs[sr_exp_def] >>
    EXP_GOAL_TYP_IH_TAC
    ,
    OPEN_EXP_TYP_TAC ``e_cast (cast_unsigned n) (e_v (v_bit bitv))`` >>
    gvs[Once e_typ_cases] >>
    gvs[Once e_typ_cases] >>
    gvs[Once v_typ_cases] >>
    gvs[Once v_typ_cases] >>
    METIS_TAC[bv_casting_length2],
    
    OPEN_EXP_TYP_TAC ``e_cast (cast_unsigned n) (e_v (v_bool b'))`` >>
    gvs[Once e_typ_cases] >>
    gvs[Once e_typ_cases] >>
    gvs[Once v_typ_cases] >>
    gvs[Once v_typ_cases] >>
    METIS_TAC[bool_casting_length, clause_name_def],

    OPEN_EXP_TYP_TAC ``e_cast cast_bool (e_v (v_bit bitv))`` >>
    gvs[Once e_typ_cases] >>
    gvs[Once e_typ_cases] >>
    gvs[Once v_typ_cases] >>
    gvs[Once v_typ_cases] >>
    METIS_TAC[bool_casting_length, clause_name_def],

    OPEN_EXP_TYP_TAC ``e_cast cast_bool (e_v (v_bool b'))`` >>
    gvs[Once e_typ_cases] >>
    gvs[Once e_typ_cases] >>
    gvs[Once v_typ_cases] >>
    gvs[Once v_typ_cases] >>
    METIS_TAC[bool_casting_length, clause_name_def]
    ]
    ,
    
 fs[] >>
 gvs[Once e_sem_cases] >>
 OPEN_EXP_TYP_TAC ``(e_cast c e)`` >>
 rfs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][e_resulted_frame_is_WT]
]

,

(****************)
(*  binop       *)
(****************)  



rpt strip_tac  >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
rpt strip_tac >| [

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
rpt strip_tac >| [

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
rpt strip_tac >|[

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
rpt strip_tac >| [

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


   Q.EXISTS_TAC `MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list` >>
   fs[] >> rw[] >>

   ‘WT_c
         (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,
          get_oracle_index,set_oracle_index,random_oracle) order
         t_scope_list_g delta_g delta_b delta_x delta_t Prs_n’ by (
    metis_tac[WT_c_ec]
   ) >>
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


   subgoal `i < LENGTH e_tau_x_d_b_list` >- (
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
     ‘i_opt’,
     `t_scope_list`,
     `t_scope_list_g`,
     `t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (e # tau # x # d # bool) list ) ))`,
     `(EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) (e_tau_x_d_b_list : (e # tau # x # d # bool) list ) ))`,
     `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
     `f'`, `f_called` , `stmt_called`,  `copied_in_scope`,‘Prs_n’ ,‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’, ‘oracle_index’, ‘random_oracle’])) o
    SIMP_RULE (srw_ss()) [sr_exp_def]) >>
   gvs[] >>


   Q.EXISTS_TAC `
   ZIP ( MAP (λ(e_,e'_,x_,d_). e'_) e_e'_x_d_list ,
         ZIP ( (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list),
         ZIP ( (MAP (λ(e_,tau_,x_,d_,b_). x_) e_tau_x_d_b_list) ,           
        ZIP ( (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list) ,
     (LUPDATE b' i (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list)))))) ` >>


   rw[map_distrub_penta] >>
   IMP_RES_TAC lemma_MAP8 >>
   fs[] >| [

     FULL_SIMP_TAC std_ss  [map_rw5_3] 
     ,

     FULL_SIMP_TAC std_ss  [map_rw5_3]  >>
     Cases_on `i=i'` >>

     fs[] >>
     fs[EL_LUPDATE] >>
     RES_TAC >>
     rw[]
     ,


     (* the direction lists are the same *)
     subgoal ` (MAP (λ(e_,e'_,x_,d_). d_) e_e'_x_d_list) =
               (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` >- 
      (
       ‘WT_c
             (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,
              get_oracle_index,set_oracle_index,random_oracle) order
             t_scope_list_g delta_g delta_b delta_x delta_t Prs_n’ by (
        metis_tac[WT_c_ec]
       ) >>
       ASSUME_TAC dir_fun_delta_same >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(MAP (λ(e_,e'_,x_,d_). (x_,d_)) (e_e'_x_d_list : (e # e # string # d) list)) `,
	 `(MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
	 `tau'`, `f`, `func_map`, `b_func_map`, `ext_map`,
	 `delta_g`, `delta_b`, `delta_x`, `apply_table_f`,
	 `order`, `t_scope_list_g`, `pars_map`, `tbl_map`, ‘get_oracle_index’, ‘set_oracle_index’, ‘random_oracle’, ‘delta_t’, ‘Prs_n’])) >>
       gvs[] >>
       IMP_RES_TAC map_simp_1 >>
       gvs[MAP_MAP_txd] >>
       gvs[MAP_FST_3_2] >>
       gvs[MAP_SND_4_2]        
	  ) >>

     (* if the arg is unred, then either out and not lval, or in and not const *)
     gvs[] >>
     IMP_RES_TAC unred_arg_index_result >| [
       (* in and not const *)
       IMP_RES_TAC dir_list_lemma1 >>
       gvs[ELIM_UNCURRY]
       ,
       (* out and lval *)
       subgoal  `(EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list)) ==>
       is_e_lval (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) ` >-
       ( RES_TAC >>
         IMP_RES_TAC e_lval_tlval ) >>

       subgoal` is_d_out (EL i (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)) ⇒
                          EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list)` >-
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


   (* first thing is showing that the args and parameters are the same
        the directions of the call in both semantics and function typing are the same
        also that the parserError string is not a name in teh arguments
        also show that the parameters have distinct names *)
   ‘WT_c
         (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,
          get_oracle_index,set_oracle_index,random_oracle) order
         t_scope_list_g delta_g delta_b delta_x delta_t Prs_n’ by (
    metis_tac[WT_c_ec]
   ) >>
   drule tfunn_imp_sig_body_lookup >>
   rpt strip_tac >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) (e_tau_x_d_b_list : (e # tau # x # d # bool) list)`,
        `tau' `, `f`])) >>
   gvs[] >>


   (* we know that stmt_called and stmt are the same, and also same
	  for xdl and the map to x d *)

   Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >>
   gvs[] >>

   (*rewrite the results of the mapping eqiiuvelence now we know that e x d lists are the same for call and typing *)      
   gvs[MAP_MAP_txd] >>
   gvs[MAP_FST_3_2] >>


         
   (* the typing scope that the new frame will have is basically the one that types the copyin*)      
   CONV_TAC $ RESORT_EXISTS_CONV rev >>                     
   Q.EXISTS_TAC `[ZIP
                    (mk_varn (MAP (λ(e_,x_,d_). x_) e_x_d_list),
                      ZIP ( MAP (λ(e_,tau_,x_,d_,b_). tau_             ) e_tau_x_d_b_list,
                            MAP (λ(e_,x_,d_). get_lval_of_e e_  ) e_x_d_list ))  ]` >>
   gvs[] >>

   SIMP_TAC list_ss [frame_typ_cases] >>
   fs[type_frame_tsl_def] >>
   fs[stmtl_typ_cases] >>
   fs[type_ith_stmt_def] >>
   fs[clause_name_def] >>

   srw_tac [boolSimps.DNF_ss][] >>
   CONV_TAC $ RESORT_EXISTS_CONV rev >>
   Q.EXISTS_TAC `tau'` >>                    
   Q.EXISTS_TAC `MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list` >>

   gvs[args_t_same_def] >>
   gvs[t_passed_elem_def] >>


   (* show not that the copied in scope is well typed and it doesn't include stars vars*)
   (* first show that the arguments are indeed well formed.*)
   gvs[] >>
   IMP_RES_TAC copyin_imp_wf_args2 >>

   gvs[map_simp_2] >>
     `ALL_DISTINCT (MAP (λ(e_,x_,d_). x_) e_x_d_list) =
     ALL_DISTINCT (MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list))` by METIS_TAC[map_simp_2] >>
   gvs[] >>

   (* then use the abstract definition of copyin *)
   IMP_RES_TAC copyin_imp >>
   gvs[] >>

   (* now we know that the domain of the copyin consist only of var names not stars*)
   ASSUME_TAC copyin_abstract_domain >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
	  `ZIP ((MAP (λ(e,x,d). d) e_x_d_list),
  	   ZIP ((MAP (λ(e,x,d). x) e_x_d_list) ,
  	   (MAP (λ(e,x,d). e) e_x_d_list)))`,
	  `scopest ⧺ gscope`, `scope'`, ‘random_oracle’])) >>

   rfs[] >>
   rfs[map_distrub] >>
   IMP_RES_TAC star_not_in_varn_list >>
   gvs[] >>

     (* now cont.  to show that the copied in scope is well typed *)
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:e`` ,
                          ``:'b`` |-> ``:string``,
                          ``:γ `` |-> ``:d``] CI_scope_list_typed)  >>
		       
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
          `e_x_d_list`, `scopest`, `t_scope_list`, `gscope`,
	  `t_scope_list_g`, `scope'`, `e_tau_x_d_b_list`,
	  ` (order,f',delta_g,delta_b,delta_x,delta_t)`])) >>
   gvs[] >>
   INST_FST [‘random_oracle’] >>
   gs[] >>

  IMP_RES_TAC wf_arg_imp_lval_consistent_single >> gvs[LENGTH_MAP] >>


         
                        
   ‘LENGTH (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list) =
    LENGTH (MAP (λ(e_,x_,d_). x_) e_x_d_list)’  by fs[]  >>


   gvs[lambda_FST] >>
   rfs[GSYM lambda_SND] >>   
   gvs[mk_varn_lemma4] >>
   gvs[map_simp_3] >>



   ‘MAP FST (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list) = MAP  (λ(e_,x_,d_). (x_)) e_x_d_list ’ by gvs[MAP_FST_3_2] >>
   lfs[] >>

   fs[MAP_MAP_txd] >>
   ‘MAP (λ(a_,b_). b_) (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list) = MAP (λ(e_,x_,d_). (d_)) e_x_d_list’ by (gvs[MAP_FST_3_2, lambda_SND ]) >>
   lfs[] >>     
                   
   drule all_func_maps_contains_welltyped_body >>
   rpt strip_tac >>      
   gvs[] >>
   
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
     `(MAP (λ(e_,x_,d_). (x_,d_)) (e_x_d_list : (e # string # d) list))`,
     `(MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
     `stmt`, `tau'`,
     `f`, ‘gscope’,
     ‘(MAP (λ(e_,x_,d_). e_) (e_x_d_list : (e # string # d) list))’])) >> gvs[] >>
   

   gvs[MAP_MAP_txd] >>
   gvs[MAP_FST_3_2] >>


   gvs[mk_varn_lemma4] >>
   gvs[map_simp_3] >>
         
   subgoal ‘type_scopes_list passed_gscope passed_tslg’ >- IMP_RES_TAC scopes_to_pass_typed_thm >>
   gvs[] >>

  rw[map_distrub] >| [
    (* prove that the called function f' t_scope is consistent with the caller's typing scope *)
    gvs[t_scopes_consistent_def] >> rpt strip_tac >>
    ASSUME_TAC wf_arg_imp_lval_typ_sinlge_list >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘e_x_d_list’,
    ‘ZIP (MAP (λ(e_,tau_,x_,d_,b_). (tau_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list) ,
          MAP (λ(e_,tau_,x_,d_,b_). (b_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list)    )’,
    ‘t’, ‘lop’,‘(order,f',delta_g,delta_b,delta_x,delta_t)’, ‘t_scope_list_g’, ‘t_scope_list’,
     ‘(scopest ⧺ gscope)’, ‘x’])) >> gvs[] >>
    gvs[map_rw_doub]
    ,
    
    (* prove that the called function f' t_scope with the sig *)
    gvs[sig_tscope_consistent_def] >>
    REPEAT GEN_TAC >> STRIP_TAC >> STRIP_TAC >>
    Cases_on ‘t_lookup_funn f delta_g passed_delta_b delta_x’ >> gvs[] >>
    gvs[extract_elem_tri_def] >> gvs[] >>
    ‘LENGTH (mk_varn (MAP (λ(e_,x_,d_). x_) e_x_d_list)) = LENGTH (e_x_d_list)’  by gvs[mk_varn_LENGTH, LENGTH_MAP] >>
    gvs[map_distrub, LENGTH_MAP] >>
    gvs[MAP_MAP_txd]
   ,

        
   gvs[MAP_MAP_txd] >>
   ‘LENGTH (mk_varn (MAP (λ(e_,x_,d_). x_) e_x_d_list)) = LENGTH (e_x_d_list)’ by gvs[mk_varn_LENGTH, LENGTH_MAP] >>
   gvs[map_distrub, LENGTH_MAP]
                  
        
   ,     

   rpt strip_tac >>
   rw[] >>
  
   gvs[MAP_MAP_txd] >>
   gvs[MAP_FST_3_2]>>
   ‘MAP (λ(e_,x_,d_). get_lval_of_e e_) e_x_d_list =
    MAP (λe. get_lval_of_e e) (MAP (λ(e_,x_,d_). e_) e_x_d_list)’
     by (gvs[MAP_MAP_o, combinTheory.o_DEF] >> gvs[ELIM_UNCURRY])  >>
   gvs[]
        
     ]

 ,


 (*second subgoal of frame creation part *) 
 (* type frame with IH usage *)

 subgoal `i < LENGTH e_e'_x_d_list` >- (
 IMP_RES_TAC unred_arg_index_in_range >>
 METIS_TAC[LENGTH_MAP] ) >>


 subgoal `i < LENGTH e_tau_x_d_b_list` >- (
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
  `(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map,oracle_index,random_oracle)`,
  `gscope`,
  `scopest`,
  `(EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list ) ) )`,
  `e''`,
  `f_called`,`stmt_called`,`copied_in_scope`,
  ‘i_opt’,
  `t_scope_list_g`,`t_scope_list`,
  `order`,
  `delta_g`,`delta_b`,`delta_x`,`delta_t`,
  `f'`,  `ty`,
  `(EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list )   ))`,
  `t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (e # tau # string #  d # bool) list ) ))`
  ])) >>
 gvs[]
 ] 
]

,

(****************)
(*  select      *)
(****************)

rpt strip_tac >>
SIMP_TAC list_ss [sr_exp_def] >>
rpt strip_tac >| [
 OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 fs[] >| [
  (* e_sel v *)
   rw[] >>
   OPEN_EXP_TYP_TAC ``(e_select (e_v v) l s)`` >>
   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   rfs[clause_name_def] >>
   OPEN_EXP_TYP_TAC ``(e_v v)`` >>
   rfs[clause_name_def] >>
   rw[] >>
   SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
   rfs[clause_name_def] >>
   SIMP_TAC (srw_ss()) [sel_def] >>
   Cases_on `v` >> (
    gs[]
   ) >>
   Cases_on `FIND (λ(s_list,x'). match_all (ZIP (SND (UNZIP l),s_list)))
               (MAP (λ(s_list_,x_,s_t_list_). (s_list_,x_))
                  s_list_x_s_t_list_list)` >> (
    fs[] >>
    fs[FIND_def] >>
    PairCases_on `z` >>
    fs[] >>
    IMP_RES_TAC index_mem >>
    IMP_RES_TAC mem_fst_snd >>
    fs[ELIM_UNCURRY] >>
    EVAL_TAC >>
    rw[]
   ) >- (
    subgoal ‘(MAP SND (MAP (λx. (FST x,FST (SND x))) s_list_x_s_t_list_list)) = (MAP (λx. FST (SND x)) s_list_x_s_t_list_list)’ >- (
     subgoal ‘?s_list x_s_t_list_list. s_list_x_s_t_list_list = ZIP (s_list, x_s_t_list_list) /\ LENGTH s_list = LENGTH x_s_t_list_list’ >- (
      qexistsl_tac [‘MAP FST s_list_x_s_t_list_list’, ‘MAP SND s_list_x_s_t_list_list’] >>
      gvs[ZIP_MAP_FST_SND]
     ) >>
     gs[GSYM ZIP_MAP] >>
     gs[MAP_ZIP] >>
     subgoal ‘((\x. FST (SND x)):(s list # string # s_t list) -> string) = (FST o SND)’ >- (
      gs[combinTheory.o_DEF]
     ) >>
     gs[MAP_ZIP]
    ) >>
    gs[]
   ),

   (* e_sel e *)
   rw[] >>
   OPEN_EXP_TYP_TAC ``(e_select e l s)`` >>
   SIMP_TAC (srw_ss()) [Once e_typ_cases] >>
   rfs[clause_name_def] >>
   gvs[] >>
   Q.PAT_X_ASSUM `sr_exp e ty`
    ((STRIP_ASSUME_TAC o (Q.SPECL
     [`e'''`,`gscope`,`scopest`,`framel`,‘i_opt’,`t_scope_list`,`t_scope_list_g`,`t_tau (tau_xtl struct_ty x'_tau_list)`,
      `b'`,`order`,`delta_g`,`delta_b`,`delta_t`,`delta_x`,`f` ])) o
    SIMP_RULE (srw_ss()) [sr_exp_def]) >>
   gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`,`stmt`,`s'`,‘Prs_n’,`apply_table_f`, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’, ‘oracle_index’, ‘random_oracle’])) >>
   fs[clause_name_def] >> gvs[] >>
   qexists_tac `s_list_x_s_t_list_list` >>
   qexists_tac `x'_tau_list` >>
   qexists_tac `struct_ty` >>
   qexists_tac `b''` >>
   gvs[] >>
   imp_res_tac e_sem_struct
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

rpt strip_tac >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
rpt strip_tac >| [

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
    ‘i_opt’,
    `t_scope_list`,
    `t_scope_list_g`,
    `t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list: (string # e # tau # bool) list )  ))`,
    `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list: (string # e # tau # bool) list)  ))`,
    `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
    `f`, `f_called` , `stmt_called`,  `copied_in_scope` ,‘Prs_n’,‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’, ‘oracle_index’, ‘random_oracle’])) o
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

 irule e_resulted_frame_is_WT >>
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
 fsrw_tac [] [] >>
 metis_tac[]
]

,

(*****************)
(*    header     *)
(*****************)

(*Same proof as above.*)



rpt strip_tac >>
SIMP_TAC (srw_ss()) [sr_exp_def] >>
rpt strip_tac >| [

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
     ‘i_opt’,
    `t_scope_list`,
    `t_scope_list_g`,
    `t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list: (string # e # tau # bool) list )  ))`,
    `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list: (string # e # tau # bool) list)  ))`,
    `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`,
    `f`, `f_called` , `stmt_called`,  `copied_in_scope`, ‘Prs_n’,‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’, ‘oracle_index’, ‘random_oracle’])) o
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

 irule e_resulted_frame_is_WT >>
 gs[] >>
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
 fsrw_tac [] [] >>
 metis_tac[]
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
rpt strip_tac >>
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
rpt strip_tac >>
fs[]
]
QED




val _ = export_theory ();
