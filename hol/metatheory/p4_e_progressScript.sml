
Theory p4_e_progress
Ancestors
  arithmetic list p4 p4_aux option ott pair rich_list alist p4_e_subject_reduction
Libs
  simpLib

fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_sem_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_sem_cases] thm)))

fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))


fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t ^exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))



(******    Type progress for expressions  ******)
Definition prog_exp_def:
prog_exp (e) (ty:'a itself) =
 !gscope (scopest:scope list) t_scope_list t_scope_list_g
 T_e tau b (c:'a ectx) order delta_g delta_b (delta_t:delta_t) delta_x f Prs_n.
     	 
          type_scopes_list gscope t_scope_list_g ∧
          type_scopes_list scopest t_scope_list ∧
	  star_not_in_sl (scopest) ∧
	  ~(is_const e) ∧
          e_typ (t_scope_list_g,t_scope_list) T_e e tau b ∧
          (T_e = (order,  f, (delta_g, delta_b, delta_x, delta_t))) /\	  
	  WT_ec c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ==>
          ?e' framel. e_red c gscope scopest e e' framel
End




(****** Type progress for expression list ******)
Definition prog_exp_list_def:
prog_exp_list (l : e list) (ty:'a itself) = 
       !(e : e). MEM e l ==> prog_exp (e) (ty:'a itself)
End


(****** Type progress for strexp list ******)
Definition prog_strexp_list_def:
prog_strexp_list (l : (string#e) list) (ty:'a itself)
      = !  (e:e) . MEM e (SND (UNZIP l)) ==> prog_exp(e) (ty:'a itself)
End


(****** Type progress for str e tup list ******)
Definition prog_strexp_tup_def:
prog_strexp_tup (tup : (string#e)) (ty:'a itself)
      =  prog_exp ((SND tup)) (ty:'a itself)
End





Theorem INDEX_FIND_concat3:
! P sl gsl.
INDEX_FIND 0 P (sl ⧺ gsl) = NONE <=>
(INDEX_FIND 0 P (sl) = NONE /\
 INDEX_FIND 0 P (gsl) = NONE)
Proof
rw[] >>
rpt strip_tac>>
fs[INDEX_FIND_NONE_EXISTS]
QED



Theorem find_topmost_map_concat_none:
! sl gsl v .
find_topmost_map (sl ⧺ gsl) v = NONE <=>
(find_topmost_map (sl) v  = NONE /\
 find_topmost_map (gsl) v  = NONE ) 
Proof
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
QED



Theorem topmost_map_concat_none[local]:
! sl gsl v .
topmost_map (sl ⧺ gsl) v = NONE <=>
(topmost_map (sl) v = NONE /\
 topmost_map (gsl) v = NONE )
Proof
rpt strip_tac >>
fs[topmost_map_def] >>
fs[] >>

Cases_on `find_topmost_map (sl ⧺ gsl) v` >>
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
QED



Theorem topmost_map_not_none[local]:
! l v x .
topmost_map l v = SOME x ==>
~(ALOOKUP x v = NONE)
Proof
fs[topmost_map_def] >>
fs[find_topmost_map_def] >>
REPEAT STRIP_TAC >>
Cases_on `INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc v)) l` >>
fs[] >>
PairCases_on `x'` >> 
gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0]
QED



Theorem lookup_map_concat_none:
! sl gsl v .
lookup_map (sl ⧺ gsl) (v) = NONE <=>
(lookup_map (sl) (v) = NONE /\
 lookup_map (gsl) (v) = NONE) 
Proof
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
 Cases_on `ALOOKUP x' v` >>
 gvs[] >> 

 IMP_RES_TAC topmost_map_not_none
]
QED




Theorem R_implies_ALOOKUP_scopes:
! R x v t sc tc.
 similar R tc sc ==>

(((SOME t = ALOOKUP tc x) ==>
(? v . SOME v = ALOOKUP sc x  /\ R t v )) /\
((SOME v = ALOOKUP sc x) ==>
(? t . SOME t = ALOOKUP tc x  /\ R t v )))
Proof

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
 Cases_on `h'0 = x` >>
 fs[] >> gvs[] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`R`, `x`, `v`, `t'`, `sc`])) >> gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][]
]
QED




Theorem R_ALOOKUP_NONE_scopelist[local]:
! R v x t scl tcl.
 similarl R tcl scl ==>
((NONE = find_topmost_map scl x)  <=>
(NONE = find_topmost_map tcl x ) )
Proof
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
   ]
   
)>>

RW_TAC list_ss [similarl_def, similar_def] >>
EVAL_TAC
QED







Theorem R_implies_topmost_map_scopesl:
!R x l1 l2 scl tcl.
   similarl R tcl scl ⇒
   (SOME l1 = topmost_map tcl x ⇒
           ? l2'. SOME l2' = topmost_map scl x ∧ similar R l1 l2') /\
   (SOME l2 = topmost_map scl x ⇒
           ? l1'. SOME l1' = topmost_map tcl x ∧ similar R l1' l2)
Proof

reverse (Induct_on `tcl` >>
         Induct_on `scl` ) >- (

 rpt strip_tac >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`R`, `x`,`l1`, `l2`, `scl`])) >>

 fs[topmost_map_def] >>
 gvs[] >>

 Cases_on `find_topmost_map (h'::tcl) x` >> gvs[] >>
 Cases_on `find_topmost_map (h::scl) x` >> gvs[] >| [
   IMP_RES_TAC R_ALOOKUP_NONE_scopelist >> gvs[]
   ,
   PairCases_on `x'` >>
   PairCases_on `x''` >>
   gvs[] >>

   IMP_RES_TAC R_find_topmost_map_scopesl >> gvs[] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`(x'0,l1)`])) >>
   gvs[]
   ,
   IMP_RES_TAC R_ALOOKUP_NONE_scopelist >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >>
   gvs[]
   ,
   PairCases_on `x'` >>
   PairCases_on `x''` >>
   gvs[] >>

   IMP_RES_TAC R_find_topmost_map_scopesl >> gvs[] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`,`(x'0,x'1)`])) >>
   gvs[]
   ]

) >>

fs[topmost_map_def, find_topmost_map_def, similar_def, similarl_def] >>
fs[INDEX_FIND_def]

QED






Theorem R_implies_lookup_map_scopesl:

! R v x t (scl :(varn # β) list list) (tcl :(varn # α) list list).
similarl R tcl scl ==>
  ((SOME t = lookup_map tcl x ==> ? v . SOME v = lookup_map scl x /\ (R t v)) /\
   (SOME v = lookup_map scl x ==> ? t . SOME t = lookup_map tcl x /\ (R t v)))
Proof

REPEAT STRIP_TAC >>
fs[lookup_map_def] >>

Cases_on `topmost_map tcl x` >>
Cases_on `topmost_map scl x` >>
gvs[] >| [

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
QED




Theorem varn_tau_exists_in_scl_tscl:
! gsl gtsl sl tsl varn v tau .
   type_scopes_list gsl gtsl ∧
   type_scopes_list sl tsl  ==>
   
    ((SOME v = lookup_vexp2 sl gsl varn ==> ?tau. SOME tau = lookup_tau tsl gtsl varn /\
                                                    v_typ v (t_tau tau) F)
						    /\
     (SOME tau = lookup_tau tsl gtsl varn ==> ?v. SOME v = lookup_vexp2 sl gsl varn /\
                                                    v_typ v (t_tau tau) F))
Proof

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

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x'`, `varn`, `(v,x1)`])) >>
 gvs[] >>
 PairCases_on ‘x'’ >> gvs[]
 ,
        
 drule R_implies_lookup_map_scopesl >>
 rpt strip_tac >> 
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`, `varn`, `x`])) >>
 gvs[]
 ,

 PairCases_on `x` >> gvs[] >>

 drule R_lookup_map_scopesl >>
 rpt strip_tac >>

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x'`, `varn`, `(x0,x1)`])) >>
  PairCases_on ‘x'’ >> gvs[]
]
QED




Theorem star_tau_exists_in_scl_tscl:
! gsl gtsl sl tsl v tau f.
star_not_in_sl (sl) /\
type_scopes_list gsl gtsl ==>

(SOME tau = find_star_in_globals gtsl (varn_star f) ⇒
           ?v. SOME v = lookup_vexp2 sl gsl (varn_star f))
	   /\
(SOME v = lookup_vexp2 sl gsl (varn_star f) ⇒
           ?tau. SOME tau = find_star_in_globals gtsl (varn_star f))
Proof

gvs[lookup_tau_def] >>
fs[lookup_vexp2_def] >>
fs[find_star_in_globals_def] >>
rpt strip_tac >| [

 Cases_on `lookup_map gtsl (varn_star f)` >>
 Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >>
 gvs[] >| [

   `lookup_map (sl)  (varn_star f) = NONE /\
    lookup_map (gsl) (varn_star f) = NONE` by
    (IMP_RES_TAC lookup_map_concat_none >> gvs[] ) >>
    
   fs[star_not_in_sl_def] >>
   gvs[type_scopes_list_def] >>
   
   drule R_implies_lookup_map_scopesl >>
   rpt strip_tac >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`x`, `(varn_star f)`, `(x0,x1)`])) >>
   gvs[]
   ,
   PairCases_on `x'` >> gvs[]
 ]
,

 Cases_on `lookup_map gtsl (varn_star f)` >>
 Cases_on `lookup_map (sl ⧺ gsl) (varn_star f)` >>
 gvs[] >>
 
 PairCases_on `x` >>
 gvs[] >>
 
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
QED





Theorem FIND_in_typl_imp_rec[local]:
!l x0 tau s.
 FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) l) = SOME (x0,tau) ==>
    (∃v'. FIND (λ(k,v). k = s) (MAP (λ(x_,v_,tau_). (x_,v_)) l) = SOME (s,v') /\
     s=x0 )
Proof
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
QED




Theorem correct_field_type_FIND:
! s tau l  .
correct_field_type (MAP (λ(x_,v_,tau_). (x_,tau_)) l) s tau ==>
  ∃v'. FIND (λ(k,v). k = s) (MAP (λ(x_,v_,tau_). (x_,v_)) l) = SOME (s,v')
Proof

gvs[correct_field_type_def] >>
fs[tau_in_rec_def] >>
REPEAT STRIP_TAC >>

Cases_on `FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) l)` >>
fs[] >>
PairCases_on `x` >> fs[] >>
Cases_on `x1 = tau` >> gvs[] >>
IMP_RES_TAC FIND_in_typl_imp_rec >>
 srw_tac [SatisfySimps.SATISFY_ss][]
QED





Theorem is_const_val_exsist:
! e . is_const e <=> (?v . e = e_v v) 
Proof
Cases_on `e` >>
fs[is_const_def]
QED



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
ONCE_REWRITE_TAC [bitv_binop_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][] 
);


val bv_bv_opl = map bv_bv_prog [ ``binop_mul``,  ``binop_add``,   ``binop_div``,   ``binop_mod``,
                            ``binop_sub``, ``binop_shl``, ``binop_shr``, `` binop_and``,
			    ``binop_or``, ``binop_xor`` ];
*)



Theorem bv_bv_prog[local]:
! bitv bitv' oper.
bs_width bitv > 0 /\ bs_width bitv <= 64 /\
bs_width bitv = bs_width bitv' /\
is_bv_op(oper) ==>
∃bitv''. bitv_binop (oper) bitv bitv' = SOME bitv''
Proof
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
ONCE_REWRITE_TAC [bitv_binop_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][]
QED



Theorem bv_bv_bool_prog[local]:
! bitv bitv' op.
bs_width bitv > 0 /\
bs_width bitv <= 64 /\
bs_width bitv = bs_width bitv' /\
is_bv_bool_op(op) ==>
  ∃b. bitv_binpred op bitv bitv' = SOME b
Proof
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
ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
fs[] >>
srw_tac [numSimps.SUC_FILTER_ss][]
QED





Theorem not_const_unred_mem[local]:
! el .
¬is_consts el ==>
(? i . i <LENGTH el /\ unred_mem_index el = SOME i)
Proof
REPEAT STRIP_TAC>>
FULL_SIMP_TAC std_ss [unred_mem_index_def] >>
Cases_on `unred_mem el` >>
fs[is_consts_def, unred_mem_def] >>

FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
IMP_RES_TAC not_index_none_exist >>

PairCases_on `x` >>
gvs[INDEX_FIND_EQ_SOME_0]
QED



Theorem unred_mem_is_const[local]:
!l i. i < LENGTH l /\ unred_mem_index l = SOME i  ==>
~is_const (EL i (l))
Proof
REPEAT STRIP_TAC >>
fs[unred_mem_index_def] >>

Cases_on `unred_mem l` >> gvs[] >>
PairCases_on `x` >> gvs[] >>

gvs[unred_mem_def] >>
IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >>
gvs[]
QED



Theorem unred_arg_eq[local]:
! dl el .  
unred_arg_index dl el ≠ NONE <=>
? i . unred_arg_index dl el  = SOME i
Proof
fs[unred_arg_index_def] >>
rpt strip_tac >>
Cases_on `find_unred_arg dl el` >>
gvs[] >>
PairCases_on `x` >> gvs[]
QED




Theorem correct_field_access[local]:
! x_v_tau_list s tau' v boolv.
correct_field_type (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list) s tau' /\
(v = v_header boolv \/ v = v_struct )==>
∃v'. acc_f (v (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list)) s =
            SOME v'
Proof
REPEAT STRIP_TAC >>
gvs[] >>
fs[acc_f_def] >>
CASE_TAC >>
IMP_RES_TAC correct_field_type_FIND >>
gvs[]
QED




Theorem e_T_get_lval[local]:
! e gtsl tsl gscope scopest T_e tau .
e_typ (gtsl,tsl) T_e e (tau) T ==>
? v . get_lval_of_e e = SOME (v)
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC e_lval_tlval >>
fs[is_e_lval_def] >>
Cases_on `get_lval_of_e e` >> gvs[]
QED








Theorem is_get_lval[local]:
!e . is_e_lval e <=> ? lval . get_lval_of_e e = SOME lval
Proof
fs[is_e_lval_def] >>
  STRIP_TAC >>
  Cases_on `get_lval_of_e e` >> gvs[]
QED






Theorem INDEX_FIND_same_list_2:
! l s i i' s' s'' v t .
INDEX_FIND 0 (λ(k,v). k = s) (MAP (λ(x,v,t). (x,v)) l) = SOME (i,s',v) /\
INDEX_FIND 0 (λ(xm,tm). xm = s) (MAP (λ(x,v,t). (x,t)) l) = SOME (i',s'',t) ==>
(i = i' /\ s = s'' /\ s = s /\ i < LENGTH l /\
v = EL i (MAP (λ(x,v,t). v) l) /\
t = EL i (MAP (λ(x,v,t). t) l)
 )
Proof 

REPEAT GEN_TAC >>
STRIP_TAC >>

subgoal `
   i' < LENGTH (MAP (λ(x,v,t). (x,t)) l) /\
    i < LENGTH (MAP (λ(x,v,t). (x,v)) l)  /\
    EL i' (MAP (λ(x,v,t). (x,t)) l) = (s'',t) /\
    EL i  (MAP (λ(x,v,t). (x,v)) l) = (s' ,v) /\
     (λ(xm,tm). xm = s) (s'',t) /\
     (λ(k ,v ). k  = s) (s' ,v)`  >- (IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]) >>
    
gvs[] >>

IMP_RES_TAC INDEX_FIND_same_list >> gvs[] >>
gvs[EL_simp5]
QED




Theorem FIND_same_list[local]:
! l s s' s'' v t .
FIND (λ(k,v). k = s) (MAP (λ(x,v,t). (x,v)) l) =
        SOME (s',v) /\
FIND (λ(xm,tm). xm = s) (MAP (λ(x,v,t). (x,t)) l) =
        SOME (s'',t) ==>	
(s = s'' /\ s = s /\ 
? i i' . i < LENGTH l  /\ i = i' /\
   v = EL i (MAP (λ(x,v,t). v) l) /\
   t = EL i (MAP (λ(x,v,t). t) l))
Proof
REPEAT GEN_TAC >>
STRIP_TAC >>
fs[FIND_def] >>
PairCases_on `z` >>
PairCases_on `z'` >>
gvs[] >>
IMP_RES_TAC INDEX_FIND_same_list_2 >>
gvs[] >>
Q.EXISTS_TAC `z'0` >>
gvs[]
QED







Theorem var_lval_is_typed[local]:
! e v tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
e_typ (gtsl,tsl) T_e (e_var v) tau T ==>
        ∃lval v'.
          get_lval_of_e (e_var v) = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v' ∧ v_typ v' tau F
Proof
rw[] >>
`∃v'. get_lval_of_e (e_var v) = SOME v'`  by (IMP_RES_TAC e_T_get_lval >> gvs[]) >>
gvs[] >>

Cases_on `v` >> 
fs[Once e_typ_cases] >>
gvs[]  >| [

 (`? v'' . SOME v'' = lookup_vexp2 scopest gscope (varn_name s) ` by
 (IMP_RES_TAC varn_tau_exists_in_scl_tscl >>
  srw_tac [SatisfySimps.SATISFY_ss][])) >>

 fs[get_lval_of_e_def] >>
 fs[lookup_vexp2_def] >>
 Cases_on `lookup_map (scopest ⧺ gscope) (varn_name s)` >>
 gvs[] >>

 fs[lookup_lval_def, lookup_v_def] >>
 PairCases_on `x` >>
 gvs[] >>

 fs[lookup_tau_def] >>
 Cases_on `lookup_map (tsl ⧺ gtsl) (varn_name s)` >>
 gvs[] >>

 `type_scopes_list (scopest ⧺ gscope) (tsl ⧺ gtsl)` by
  (IMP_RES_TAC type_scopes_list_APPEND) >>
 gvs[type_scopes_list_def] >>


 ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                        ``:'b`` |-> ``:(tau#lval option)``] R_lookup_map_scopesl)  >>
			 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)’ , `(x)`, `(varn_name s)`,
  `(v'',x1)`, `(tsl ⧺ gtsl)`,`(scopest ⧺ gscope)`])) >>
 PairCases_on ‘x’ >> gvs[]
 ,
 
 (`? v'' . SOME v'' = lookup_vexp2 scopest gscope (varn_star f) ` by
 (IMP_RES_TAC star_tau_exists_in_scl_tscl >>
 srw_tac [SatisfySimps.SATISFY_ss][])) >>

 fs[get_lval_of_e_def] >>
 fs[lookup_vexp2_def] >>
 Cases_on `lookup_map (scopest ⧺ gscope) (varn_star f)` >>
 gvs[] >>

 fs[lookup_lval_def, lookup_v_def] >>
 PairCases_on `x` >>
 gvs[] >>

 fs[find_star_in_globals_def] >>
 Cases_on `lookup_map gtsl (varn_star f)` >>
 gvs[] >>

 IMP_RES_TAC lookup_map_in_gsl_lemma >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`v''`, `x1`, `gscope`, `f`])) >>
 gvs[] >>

 ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                        ``:'b`` |-> ``:(tau#lval option)``] R_lookup_map_scopesl)  >>

		 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)’, `x`, `(varn_star f)`,
  `(v'',x1)`, `(gtsl)`,`(gscope)`])) >>
 gvs[type_scopes_list_def] >>
 PairCases_on ‘x’ >> gvs[]
]
QED




Theorem e_lval_WT:
! e x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
is_e_lval e /\
e_typ (gtsl,tsl) T_e e tau T /\
(!lval. get_lval_of_e e = SOME lval ==> lval_unred_index lval = NONE /\ ~lval_oob (scopest ⧺ gscope) lval) ==>
        (∃lval v.
          get_lval_of_e e = SOME lval ∧
          lookup_lval (scopest ⧺ gscope) lval = SOME v /\
	  v_typ v tau F)
Proof    
	  

Induct >>
REPEAT STRIP_TAC >~ [`∃lval v. get_lval_of_e (e_acc e s) = SOME lval ∧
                               lookup_lval (scopest ⧺ gscope) lval = SOME v ∧
	                       v_typ v tau F`] >- (

 fs[] >>
 (subgoal `? v . get_lval_of_e (e_acc e s) = SOME v` >-
   ( IMP_RES_TAC e_T_get_lval >>
     gvs[])  >>
   gvs[]) >>


 OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
 fs[] >>
 Cases_on `struct_ty` >>
 gvs[] >>


 (subgoal `? v . get_lval_of_e (e) = SOME v` >-
  (IMP_RES_TAC e_T_get_lval >> gvs[])  >>
    gvs[clause_name_def]) >>

 ‘lval_unred_index v' = NONE /\ ~lval_oob (scopest ⧺ gscope) v'’ by (
  gvs[get_lval_of_e_def, lval_unred_index_def, lval_oob_def]
 ) >>

 fs[is_get_lval] >| [

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(t_tau (tau_xtl struct_ty_struct x_tau_list))`,
	 `gtsl`, `gscope`,`tsl`,`scopest`,`T_e`])) >> gvs[] >>

   Q.PAT_X_ASSUM `get_lval_of_e (e_acc e s) = SOME v`
   ( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [get_lval_of_e_def] ) >>
   gvs[] >>

   OPEN_V_TYP_TAC ``v''`` >>
   fs[] >>
   gvs[] >>

   IMP_RES_TAC correct_field_type_FIND >>
   fs[lookup_lval_def] >>
   fs[acc_f_def] >>
   fs[correct_field_type_def] >>
   fs[tau_in_rec_def] >>
   Cases_on `FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` >>
   gvs[] >>

   PairCases_on `x` >> gvs[] >>
   Cases_on `x1 = tau'` >> gvs[] >>
   IMP_RES_TAC FIND_same_list >>
   gvs[]
   ,

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `(t_tau (tau_xtl struct_ty_header x_tau_list))`,
	 `gtsl`, `gscope`,`tsl`,`scopest`,`T_e`])) >> gvs[] >>

   Q.PAT_X_ASSUM `get_lval_of_e (e_acc e s) = SOME v`
   ( STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [get_lval_of_e_def] ) >>
   gvs[] >>

   OPEN_V_TYP_TAC ``v''`` >> fs[] >>
   gvs[] >>

   IMP_RES_TAC correct_field_type_FIND >>
   fs[lookup_lval_def] >>
   fs[acc_f_def] >>
   fs[correct_field_type_def] >>
   fs[tau_in_rec_def] >>
   Cases_on `FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)` >>
   gvs[] >>

   PairCases_on `x` >> gvs[] >>
   Cases_on `x1 = tau'` >> gvs[] >>
   IMP_RES_TAC FIND_same_list >>
   gvs[]
   ]

) >~ [`∃lval v. get_lval_of_e (e_slice e e' e'') = SOME lval ∧
                lookup_lval (scopest ⧺ gscope) lval = SOME v ∧
		v_typ v tau F`] >- (


 OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >> fs[] >>
 
 `(? v''' . get_lval_of_e (e) = SOME v''')` by
   (IMP_RES_TAC e_T_get_lval >> gvs[]) >>

 gvs[is_get_lval, get_lval_of_e_def] >>
 fs[lval_unred_index_def, lval_oob_def] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(t_tau (tau_bit w))`, `gtsl`,
  `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[] >>

 fs[Once v_typ_cases] >>
 SIMP_TAC list_ss [lookup_lval_def] >> gvs[] >>
 PairCases_on `bitv''` >>
 gvs[] >>

 fs[slice_lval_def] >>
 PairCases_on `bitv` >> PairCases_on `bitv'` >>
 gvs[] >>

 gvs[slice_def, bs_width_def, bitv_bitslice_def, vec_to_const_def]

) >~ [`∃lval v. get_lval_of_e (e_index e e') = SOME lval ∧
                lookup_lval (scopest ⧺ gscope) lval = SOME v ∧
		v_typ v tau F`] >- (

 (* Header stack element *)
 OPEN_EXP_TYP_TAC ``(e_index e e')`` >>
 fs[] >>

 `(? v''' . get_lval_of_e (e) = SOME v''')` by (
  IMP_RES_TAC e_T_get_lval >>
  gvs[]
 ) >>

 gvs[is_get_lval, get_lval_of_e_def] >>
 fs[lval_unred_index_def, lval_oob_def] >>

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(t_tau (tau_stack tau' w'))`, `gtsl`,
  `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[AllCaseEqs()] >>

 OPEN_V_TYP_TAC ``v`` >>
 gvs[] >>
 gvs[is_const_val_exsist] >>
 OPEN_EXP_TYP_TAC ``(e_v v)`` >>
 gvs[] >>
 OPEN_V_TYP_TAC ``v`` >>
 gvs[] >>
 PairCases_on `bitv` >>
 gvs[lookup_lval_def, oEL_THM]

) >~ [` ∃lval v'. get_lval_of_e (e_var v) = SOME lval ∧
                  lookup_lval (scopest ⧺ gscope) lval = SOME v' ∧
		  v_typ v' tau F `] >- (
		  
IMP_RES_TAC var_lval_is_typed >> gvs[]

) >~ [` ∃lval v'. get_lval_of_e (e_saved e v) = SOME lval ∧
                  lookup_lval (scopest ⧺ gscope) lval = SOME v' ∧
		  v_typ v' tau F `] >- (

 OPEN_EXP_TYP_TAC ``(e_saved e v)`` >> fs[] >>
 gvs[get_lval_of_e_def, is_e_lval_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`tau`, `gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[is_e_lval_def]

) >>

fs[get_lval_of_e_def] >>
fs[Once e_typ_cases] >>
fs[Once v_typ_cases]

QED




(* A saved argument supplies its saved value *)
Theorem saved_arg_wf[local]:
!e gtsl tsl T_e tau b ss.
is_e_saved e /\
e_typ (gtsl,tsl) T_e e tau b ==>
?lval v. get_lval_of_e e = SOME lval /\ arg_lval_v ss lval e = SOME v
Proof
rpt strip_tac >>
Cases_on ‘e’ >>
gvs[is_e_saved_def, arg_lval_v_def] >>
OPEN_EXP_TYP_TAC ``(e_saved e' v)`` >>
gvs[get_lval_of_e_def] >>
IMP_RES_TAC e_T_get_lval >>
gvs[]
QED

Theorem wf_arg_single_implied[local]:
! e d b x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
out_is_lval [d] [b] /\
is_arg_red d e /\
e_typ (gtsl,tsl) T_e  (e) (tau) (b) ==>
wf_arg d x e (scopest ⧺ gscope)
Proof
rw[] >>
rpt strip_tac >>
Cases_on `is_d_out d` >>
fs[is_arg_red_def] >>
fs[wf_arg_def] >| [
 IMP_RES_TAC saved_arg_wf >> gvs[]
 ,

 gvs[is_const_val_exsist] >>
 fs[v_of_e_def]
]
QED




Theorem wf_arg_single_implied_2[local]:
! e d b x tau gtsl gscope tsl scopest T_e .
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
is_d_out d ⇒ b /\
is_arg_red d e /\
e_typ (gtsl,tsl) T_e  (e) (tau) (b) ==>
wf_arg d x e (scopest ⧺ gscope)
Proof
rw[] >>
rpt strip_tac >>
Cases_on `is_d_out d` >>
fs[is_arg_red_def] >>
fs[wf_arg_def] >>
IMP_RES_TAC saved_arg_wf >>
IMP_RES_TAC e_lval_WT >> gvs[]
QED




Theorem wf_arg_normalization_new[local]:
! d dl x xl e el ss.
wf_arg_list (d::dl) (x::xl) (e::el) ss <=>
wf_arg d x e ss /\ wf_arg_list (dl) (xl) (el) ss
Proof
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
   `i=1` by fs[] >>
   rw[] >>
   rfs[]
   ,
   fs[PRE_SUB1] >>
   rfs[GSYM EL] >>
   gvs[ADD1]
]]
QED






Theorem check_args_red_normalize2_new[local]:
! dl el  d e . 
check_args_red (d::dl) (e::el) <=>
(check_args_red dl el /\
check_args_red [d] [e] )
Proof
fs[check_args_red_def] >>
srw_tac [boolSimps.DNF_ss][] >>
EQ_TAC >> gvs[]
QED




Theorem wf_arg_full_implied[local]:
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
              (t_tau (EL i (MAP (λ(e_,tau_,d_,b_,x_). tau_) e_tau_d_b_t_list)))
              (EL i (MAP (λ(e_,tau_,d_,b_,x_). b_) e_tau_d_b_t_list))) ==>
wf_arg_list (MAP (λ(e_,tau_,d_,b_,x_). d_) e_tau_d_b_t_list)
 	      (MAP (λ(e_,tau_,d_,b_,x_). x_) e_tau_d_b_t_list)
              (MAP (λ(e_,tau_,d_,b_,x_). e_) e_tau_d_b_t_list)
	      (scopest++gscope)
Proof
Induct >>
REPEAT STRIP_TAC >>
gvs[] >-
 fs[wf_arg_list_def] >>
 
PairCases_on `h` >> gvs[] >>

gvs[wf_arg_normalization_new] >>
gvs[out_is_lval_normalisation] >>
gvs[Once check_args_red_normalize2_new] >>

CONJ_TAC >| [

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
 gvs[] >>

 ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:string``  ] wf_arg_single_implied_2) >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`h0`, `h2`, `h3`, `h4`, `(t_tau h1)`, `gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>

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
                 (EL i (MAP (λ(e_,tau_,d_,b_,x_).   e_) e_tau_d_b_t_list))
      (t_tau (EL i (MAP (λ(e_,tau_,d_,b_,x_). tau_) e_tau_d_b_t_list)))
                 (EL i (MAP (λ(e_,tau_,d_,b_,x_).   b_) e_tau_d_b_t_list)))` >-
  (REPEAT STRIP_TAC >>

  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`i + 1` ])) >>
  gvs[ADD1] >>
  fs[EL_CONS] >>
  fs[PRE_SUB1] ) >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`gtsl`, `gscope`, `tsl`, `scopest`, `T_e`])) >>
 gvs[]
]
QED











Theorem wf_arg_full_implied_2[local]:
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
              (t_tau (EL i tl))
              (EL i bl)) ==>
wf_arg_list dl xl el (scopest++gscope)
Proof
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
QED



Theorem wf_imp_ci_abstract_single[local]:
!e d x ss random_oracle.
wf_arg d x e ss ==>
?scope. copyin_abstract [x] [d] [e] ss scope random_oracle
Proof
rpt strip_tac >>
Q.EXISTS_TAC `[(varn_name x , (\ (a,b). (FST a, b)) $ THE (one_arg_val_for_newscope d e ss oracle_index random_oracle))]` >>
fs[copyin_abstract_def] >>
rpt strip_tac >> (
 imp_res_tac wf_imp_val_lval
) >- (
 Q.PAT_X_ASSUM ‘!random_oracle i. _’ (fn thm => assume_tac $ Q.SPECL [‘random_oracle’, ‘oracle_index’] thm) >>
 gvs[]
) >>
qexists_tac ‘oracle_index’ >>
Q.PAT_X_ASSUM ‘!random_oracle i. _’ (fn thm => assume_tac $ Q.SPECL [‘random_oracle’, ‘oracle_index’] thm) >>
gs[]
QED





Theorem wf_imp_new_vlval_list[local]:
! i dl xl el ss oracle_index random_oracle.
(LENGTH xl = LENGTH dl) /\
(LENGTH dl = LENGTH el) /\
(i < LENGTH dl ) /\
wf_arg_list (dl) (xl) (el) ss ==>
? vlval . one_arg_val_for_newscope (EL i (dl)) (EL i (el)) ss oracle_index random_oracle = SOME vlval
Proof
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
 metis_tac[]
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
  ]
]
QED



Theorem wf_arg_list_NONE2[local]:
! dl xl el ss oracle_index random_oracle.
(LENGTH xl = LENGTH dl) /\
(LENGTH dl = LENGTH el) /\
wf_arg_list dl xl el ss /\
ALL_DISTINCT xl ==>
~ (all_arg_update_for_newscope xl dl el  ss oracle_index random_oracle = NONE)
Proof
REPEAT STRIP_TAC >>
fs[all_arg_update_for_newscope_def] >>
ASSUME_TAC wf_arg_list_NONE >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ZIP (dl,ZIP (xl,el))`])) >>
gvs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ss`, ‘oracle_index’, ‘random_oracle’])) >>
gvs[] >| [

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
QED




Theorem copyin_imp_rw[local]:
! xl dl el gscope scopest scope oracle_index random_oracle.
   (LENGTH xl = LENGTH dl) /\
   (LENGTH dl = LENGTH el) /\     
     (ALL_DISTINCT xl) ∧
     (wf_arg_list dl xl el  (scopest ⧺ gscope))  ==>
((?i_opt. SOME (scope, i_opt) = copyin xl dl el gscope scopest oracle_index random_oracle)
==>
copyin_abstract xl dl el (scopest ⧺ gscope) scope random_oracle)
Proof
REPEAT STRIP_TAC >>
ASSUME_TAC copyin_imp >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`ZIP (el,ZIP (xl,dl))`, `gscope`,
     `scopest`, `scope`, ‘oracle_index’, ‘random_oracle’])) >>
gvs[] >>

`(MAP (λ(e,x,d). x) (ZIP (el,ZIP (xl,dl)))) = xl` by gvs[GSYM map_distrub] >>
`(MAP (λ(e,x,d). d) (ZIP (el,ZIP (xl,dl)))) = dl` by gvs[GSYM map_distrub] >>
`(MAP (λ(e,x,d). e) (ZIP (el,ZIP (xl,dl)))) = el` by gvs[GSYM map_distrub] >>
gvs[] >>
metis_tac[]
QED








        




        

(* An l-value with an out-of-bounds stack index has no value *)
Theorem lval_oob_lookup_lval[local]:
!lval ss.
lval_oob ss lval ==>
lookup_lval ss lval = NONE
Proof
Induct_on ‘lval’ >> (
 rw[lval_oob_def, lookup_lval_def]
) >- (
 res_tac >>
 simp[]
) >>
rpt CASE_TAC >> (
 gvs[oEL_THM]
)
QED

(* The first stack index that is not a value is not a value *)
Theorem e_unred_index_not_const[local]:
!e e''.
e_unred_index e = SOME e'' ==>
~is_const e''
Proof
recInduct e_unred_index_ind >> (
 rw[e_unred_index_def] >>
 gvs[AllCaseEqs()]
)
QED

(* A typed l-value whose stack indices are values can be read, also out of bounds *)
Theorem read_lval_exists[local]:
!e tau lval gtsl gscope tsl scopest T_e i random_oracle.
star_not_in_sl scopest /\
type_scopes_list gscope gtsl /\
type_scopes_list scopest tsl /\
e_typ (gtsl,tsl) T_e e (t_tau tau) T /\
get_lval_of_e e = SOME lval /\
lval_unred_index lval = NONE ==>
?v i'. read_lval (scopest ⧺ gscope) lval i random_oracle = SOME (v, i')
Proof
Induct >> (
 rpt strip_tac >>
 fs[get_lval_of_e_def] >>
 gvs[AllCaseEqs(), lval_unred_index_def]
) >| [

 (* variables *)
 drule_all var_lval_is_typed >>
 strip_tac >>
 gvs[get_lval_of_e_def, lookup_lval_def, read_lval_def]
 ,

 (* acc *)
 OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
 gvs[] >>
 first_x_assum drule_all >>
 disch_then (qspecl_then [‘i’, ‘random_oracle’] strip_assume_tac) >>
 drule_all read_lval_typed >>
 strip_tac >>
 OPEN_V_TYP_TAC ``v`` >>
 gvs[] >>
 simp[read_lval_def] >| [
  qspecl_then [‘x_v_tau_list’, ‘s’, ‘tau’, ‘v_struct’, ‘ARB’] mp_tac correct_field_access >>
  simp[] >>
  strip_tac >>
  simp[]
  ,
  qspecl_then [‘x_v_tau_list’, ‘s’, ‘tau’, ‘v_header boolv’, ‘boolv’] mp_tac correct_field_access >>
  simp[] >>
  strip_tac >>
  simp[]
 ]
 ,

 (* slice *)
 OPEN_EXP_TYP_TAC ``(e_slice e e' e'')`` >>
 gvs[] >>
 last_x_assum drule_all >>
 disch_then (qspecl_then [‘i’, ‘random_oracle’] strip_assume_tac) >>
 drule_all read_lval_typed >>
 strip_tac >>
 OPEN_V_TYP_TAC ``v`` >>
 gvs[] >>
 PairCases_on `bitv` >>
 PairCases_on `bitv'` >>
 PairCases_on `bitv''` >>
 simp[read_lval_def, slice_lval_def]
 ,

 (* Header stack element *)
 OPEN_EXP_TYP_TAC ``(e_index e e')`` >>
 gvs[] >>
 last_x_assum drule_all >>
 disch_then (qspecl_then [‘i’, ‘random_oracle’] strip_assume_tac) >>
 drule_all read_lval_typed >>
 strip_tac >>
 OPEN_V_TYP_TAC ``v`` >>
 gvs[is_const_val_exsist] >>
 OPEN_EXP_TYP_TAC ``(e_v v)`` >>
 gvs[] >>
 OPEN_V_TYP_TAC ``v`` >>
 gvs[] >>
 PairCases_on `bitv` >>
 simp[read_lval_def, oEL_THM, stack_el_oob_def] >>
 Cases_on ‘v_list’ >> (
  gvs[]
 ) >>
 rw[] >>
 Cases_on ‘undef_v random_oracle i' h’ >>
 simp[]
 ,

 (* saved *)
 OPEN_EXP_TYP_TAC ``(e_saved e v)`` >>
 gvs[] >>
 first_x_assum drule_all >>
 simp[]
]
QED



Theorem PROG_e:
! (ty:'a itself) .
(!e. prog_exp e ty) /\
(! (l1: e list). prog_exp_list l1 ty) /\
(! (l2: (string#e) list) .  prog_strexp_list l2 ty) /\
(! tup. prog_strexp_tup tup ty)
Proof
STRIP_TAC >>
Mutual.MUTUAL_INDUCT_TAC e_unred_index_mutual_induction >| [

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
SIMP_TAC list_ss [Once e_sem_cases] >>
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
fs[Once e_sem_cases] >>
FULL_SIMP_TAC (srw_ss()) [Once e_typ_cases]

,

(*****************)
(* field access  *)
(*****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

Cases_on ‘?tau' w' b'. e_typ (t_scope_list_g,t_scope_list) (order,f,delta_g,delta_b,delta_x,delta_t) e (t_tau (tau_stack tau' w')) b'’ >- (
 (* Header stack member *)
 gvs[] >>
 Cases_on `is_const e` >| [
  gvs[is_const_val_exsist] >>
  qpat_x_assum ‘e_typ _ _ (e_v _) _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once e_typ_cases]) >>
  OPEN_V_TYP_TAC ``v`` >>
  gvs[] >>
  OPEN_EXP_TYP_TAC ``(e_acc (e_v (v_stack v_list i)) s)`` >>
  gvs[] >| [
   fs[Once e_typ_cases] >>
   fs[Once v_typ_cases]
   ,
   (* size *)
   PairCases_on `c` >>
   SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
   srw_tac [boolSimps.DNF_ss][clause_name_def]
   ,
   (* lastIndex *)
   PairCases_on `c` >>
   SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
   Cases_on ‘i’ >> (
    srw_tac [boolSimps.DNF_ss][clause_name_def]
   )
  ]
  ,
  fs[prog_exp_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
  `t_tau (tau_stack tau' w')`, ` b'`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>
  gvs[] >>
  SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
  srw_tac [boolSimps.DNF_ss][] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
 ]
) >>

OPEN_EXP_TYP_TAC ``(e_acc e s)`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
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
  `t_tau (tau_xtl struct_ty x_tau_list)`, ` b`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>
  gvs[] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,

(*****************)
(*  unary oper   *)
(*****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>
RW_TAC (srw_ss()) [Once e_sem_cases] >>

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
   `tau`, ` b'`, ` c`, ` order`, `delta_g`, ` delta_b`,
   ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>

 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,

(****************)
(*  cast       *)
(****************) 

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>
RW_TAC (srw_ss()) [Once e_sem_cases] >>

rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [
 
 gvs[clause_name_def] >>
 Cases_on `e` >>
 fs[is_const_def] >>
 gvs[Once e_sem_cases]  >>                

 (*from the typing rules we know *)
 Cases_on ‘c’ >>
 gvs[] >| [            
  OPEN_EXP_TYP_TAC ``(e_cast (cast_unsigned n) (e_v v))`` >> fs[] >>
  OPEN_EXP_TYP_TAC ``e_v v`` >> fs[] >> (
   gvs[Once e_sem_cases]  >>                
   OPEN_V_TYP_TAC ``v`` >> gvs[clause_name_def]
  ),

  OPEN_EXP_TYP_TAC ``(e_cast cast_bool (e_v v))`` >> fs[] >>
  OPEN_EXP_TYP_TAC ``e_v v`` >> fs[] >> (
   gvs[Once e_sem_cases]  >>                
   OPEN_V_TYP_TAC ``v`` >> gvs[clause_name_def]
  )
 ],
        

 OPEN_EXP_TYP_TAC ``(e_cast c e)`` >>
 fs[prog_exp_def] >>
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
   `tp`, ` b'`, ` c'`, ` order`, `delta_g`, ` delta_b`,
   ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>

 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]

  ]        
,

(****************)
(*  binop       *)
(****************)  

simp_tac list_ss [prog_exp_def] >>
rpt strip_tac >>

(* now we construct three cases on teh reduction rule,
   via checked teh cases on e being a constant
   e + e'
   v + e'
   v + v'
*)

 Cases_on `is_const e` >| [
 Cases_on `is_const e'` >| [
 
   (* case v op v *)
   
   RW_TAC (srw_ss()) [Once e_sem_cases] >>
   rw[] >>
   srw_tac [boolSimps.DNF_ss][] >>
   OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
     
   Cases_on `b` >>
   fs[is_bv_op_def, is_bool_op_def, is_err_bool_def, is_bv_bool_op_def, is_eq_op_def] >>

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>

     
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v'`` >>
   fs[tau_composite_def, v_composite_def] >>

   ASSUME_TAC bv_bv_bool_prog >> gvs[is_bv_bool_op_def]>>
   ASSUME_TAC bv_bv_prog >> gvs[is_bv_op_def]
   ,
   
   (* case v op e*)
   
   SIMP_TAC list_ss [Once e_sem_cases] >>
   OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
  
   OPEN_EXP_TYP_TAC ``(e_v v)`` >> gvs[] >>
   OPEN_V_TYP_TAC ``v`` >>

   Cases_on `b` >>
   fs[is_bv_op_def, is_bool_op_def, is_err_bool_def, is_bv_bool_op_def, is_eq_op_def] >>

   fs[clause_name_def] >>
   gvs[is_const_val_exsist] >>
   gvs[lemma_v_red_forall, is_short_circuitable_def] >>
   
   fs[] >>
   srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] >>

   fs[prog_exp_def] >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][clause_name_def, prog_exp_def] >>
   METIS_TAC []   
   ]
 ,
 
 (*case e op e'*)
 
 SIMP_TAC list_ss [Once e_sem_cases] >>
 OPEN_EXP_TYP_TAC ``(e_binop e _ e')`` >>
 fs[clause_name_def] >>
 gvs[is_const_val_exsist] >|[
   (* both IH of is_bv_op b *)
 
   fs[prog_exp_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
    `t_tau (tau_bit w)`, ` b''`, ` c`, ` order`, `delta_g`,
    ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>

   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][Once e_typ_cases]    
   ,

   (* both IH of is_bool_op b*)
   fs[prog_exp_def] >>

   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
    `t_tau (tau_bool)`, ` b''`, ` c`, ` order`, `delta_g`,
    ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]  
   ,

   (* both IH of is_err_bool b*)
   (*fs[prog_exp_def] >>
    
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
    `t_tau (tau_err)`, ` b''`, ` c`, ` order`, `delta_g`,
    ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][] 
   , *)

   (* both IH of is_bv_bool_op b *)
   fs[prog_exp_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
   `(t_tau (tau_bit w))`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>	    
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][] 
   ,

   (* both IH of is_eq_op b on varbits *)
   fs[prog_exp_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [‘gscope’, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
    ‘t_tau (tau_varbit w)’, ‘b''’, ‘c’, ‘order’, ‘delta_g’,
    ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,

   (* both IH of is_eq_op b on structs, headers and header stacks *)
   fs[prog_exp_def] >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [‘gscope’, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
    ‘t_tau tau'’, ‘b''’, ‘c’, ‘order’, ‘delta_g’,
    ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]
 ]

]

,

(****************)
(*  concat      *)
(****************)


SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_concat e e')`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
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
     `(t_tau (tau_bit w2'))`, ` b''`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’ ])) >>
	    
   gvs[] >>
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]   
   ]
 ,

  (* nested expressions cases*)

 fs[prog_exp_def] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
   `(t_tau (tau_bit w1))`, ` b'`, ` c`, ` order`, `delta_g`,
   ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’ ])) >>
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

RW_TAC (srw_ss()) [Once e_sem_cases] >>
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
   `(t_tau (tau_bit w))`, ` b`, ` c`, ` order`, `delta_g`,
   ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’])) >>
  gvs[] >>
  gvs[is_const_val_exsist] >>
  srw_tac [SatisfySimps.SATISFY_ss][]   
]

,

(****************)
(*   index      *)
(****************)

(* Header stack element *)
SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_index e e')`` >>
gvs[] >>

Cases_on `is_const e` >| [
 Cases_on `is_const e'` >| [

   (* both are values: the element, or an unspecified value out of bounds *)
   gvs[is_const_val_exsist] >>
   qpat_x_assum ‘e_typ _ _ (e_v _) (t_tau (tau_stack _ _)) _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once e_typ_cases]) >>
   OPEN_V_TYP_TAC ``v`` >>
   gvs[] >>
   OPEN_EXP_TYP_TAC ``(e_v v')`` >>
   gvs[] >>
   OPEN_V_TYP_TAC ``v'`` >>
   gvs[] >>
   PairCases_on `c` >>
   SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
   Cases_on ‘v2n (FST bitv) < LENGTH v_list’ >| [
    srw_tac [boolSimps.DNF_ss][clause_name_def, oEL_THM]
    ,
    Cases_on ‘v_list’ >> (
     gvs[]
    ) >>
    srw_tac [boolSimps.DNF_ss][clause_name_def, stack_el_oob_def] >>
    Cases_on ‘undef_v c7 c6 h’ >>
    simp[]
   ]
   ,

   (* now show that e' actually reduces from IH*)
   fs[prog_exp_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
    [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
     `(t_tau (tau_bit w))`, ` b'`, ` c`, ` order`, `
            delta_g`, ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’ ])) >>
   gvs[] >>
   gvs[is_const_val_exsist] >>
   SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
   srw_tac [boolSimps.DNF_ss][] >>
   srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
   ]
 ,

  (* nested expressions cases*)

 fs[prog_exp_def] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
  [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
   `(t_tau (tau_stack tau' w'))`, ` b`, ` c`, ` order`, `delta_g`,
   ` delta_b`, ` delta_t`, ` delta_x`,`f`, ‘Prs_n’ ])) >>
  gvs[] >>
  SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
  srw_tac [boolSimps.DNF_ss][] >>
  srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,

(****************)
(*  call        *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_call f l1)`` >>
gvs[] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>


PairCases_on `c` >> 
gvs[is_const_def, clause_name_def] >>


(* the cases should be on if there is an element unreduced yet? *)
Cases_on ` (unred_arg_index (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)
                 (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) = NONE)` >| [

 DISJ1_TAC >>
 
 IMP_RES_TAC unred_arg_index_NONE >>

 ASSUME_TAC tfunn_imp_sig_body_lookup >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, 
    ‘get_oracle_index’, ‘set_oracle_index’, ‘c7’,
    `order`, `t_scope_list_g`,
   `delta_g`, `delta_b`, `delta_x`,
   `(MAP (λ(e_,tau_,x_,d_,b_).(tau_,x_,d_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
   `tau'`, `f` , ‘delta_t’, ‘Prs_n’  ])) >> gvs[] >>
 assume_tac $ Q.SPECL
    [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, ‘get_oracle_index’, ‘set_oracle_index’, ‘c6’, ‘c7’] $ GSYM WT_c_ec >>
 gs[] >>

 Q.EXISTS_TAC `ZIP ((MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list),
                   ZIP(MAP FST xdl,MAP SND xdl))` >>

 Q.EXISTS_TAC `stmt` >>

 rfs[map_quad_zip112, map_tri_zip12] >>
 fs[GSYM UNZIP_MAP] >>

 `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
          (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
 gvs[] >> rfs[] >>


 ASSUME_TAC wf_arg_full_implied_2 >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP FST (xdl : (string # d) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). b_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). e_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). d_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `t_scope_list_g`,
    `gscope`, `t_scope_list`, `scopest`, `(order,f',delta_g,delta_b,delta_x,delta_t)`])) >>
  gvs[] >> 

 

(*show that the copyin_abstract is implied by the wfness of args *)

 ASSUME_TAC copyin_imp_rw >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`(MAP FST (xdl : (string # d) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). d_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `(MAP (λ(e_,tau_,x_,d_,b_). e_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
    `gscope`,  `scopest`, `scope`])) >>
    gvs[] >> 
    gvs[] >>
 qpat_x_assum ‘!oracle_index. _’ (fn thm => assume_tac $ Q.SPECL [‘c6’, ‘c7’] thm) >>
 Q.EXISTS_TAC `FST $ THE(copyin (MAP FST xdl) (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)
                (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) gscope scopest c6 c7)` >>
 gvs[] >>

 Cases_on `copyin (MAP FST xdl) (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)
          (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) gscope scopest c6 c7` >| [
	  
   IMP_RES_TAC wf_arg_list_NONE2 >>
   gvs[] >>
   gvs[copyin_def, AllCaseEqs()]
   ,
   gvs[] >>
   qexists_tac ‘SND x’ >>
   gs[]
   ]
 ,

 (* if we can reduce one of the args, then we should be able to progress e -> e' *)

 DISJ2_TAC >>
 IMP_RES_TAC unred_arg_eq >> 

 (* first show that we can indeed find a map for the function f in the context *)
 ASSUME_TAC tfunn_imp_sig_lookup >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`,
    ‘get_oracle_index’, ‘set_oracle_index’, ‘c7’,
   `order`, `t_scope_list_g`,
   `delta_g`, `delta_b`, `delta_x`,
   `(MAP (λ(e_,tau_,x_,d_,b_).(tau_,x_,d_)) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`,
   `tau'`, `f`, ‘delta_t’, ‘Prs_n’])) >> gvs[] >>


 (* now use IH *)
 (* we know that i is less than length of teh list *)

 IMP_RES_TAC unred_arg_index_in_range >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >> gvs[] >>

 fs[prog_exp_list_def] >>
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))`])) >> gvs[] >>

 `MEM (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list ))
            (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list )` by fs[EL_MEM] >>
 gvs[] >>
 fs[prog_exp_def] >>  
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`gscope`, `scopest`, `t_scope_list`, `t_scope_list_g`,
   `(t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list))))`,
   `(EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) (e_tau_x_d_b_list : (e # tau # string # d # bool) list)))`,
   `(c0,c1,c2,c3,c4,c5,c6,c7)`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f'`, ‘Prs_n’])) >> gvs[] >>
 IMP_RES_TAC unred_arg_index_result >| [
   DISJ1_TAC >>
   (* if d is in/none, then it shouldn't be a constant in order to reduce it *)
   gvs[] >>
   (* TODO: Why doesn't it work to rewrite? *)
   assume_tac $ Q.SPECL
      [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, ‘get_oracle_index’, ‘set_oracle_index’, ‘c6’, ‘c7’] $ GSYM WT_c_ec >>
   gs[] >>

   Q.EXISTS_TAC `framel` >>
   Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list ,
     	         ZIP (LUPDATE e' i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) ,
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
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[]
     ,
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP] >>
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[]
     ,
     rfs[map_quad_zip112] 
     ,
     rfs[map_quad_zip112] 
     ]
     
   ,
   (* if d is out, the argument is saved *)
   DISJ2_TAC >>
   subgoal ‘EL i (MAP (λ(e_,tau_,x_,d_,b_). b_) e_tau_x_d_b_list)’ >- (
    IMP_RES_TAC unred_arg_out_is_lval_imp >>
    gvs[is_d_out_def]
   ) >>
   assume_tac $ Q.SPECL
      [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, ‘get_oracle_index’, ‘set_oracle_index’, ‘c6’, ‘c7’] $ GSYM WT_c_ec >>
   gs[] >>
   ‘is_e_lval (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list))’ by (
    IMP_RES_TAC e_lval_tlval >>
    gvs[]
   ) >>
   (* a stack index of the argument that is not a value is reduced first *)
   Cases_on ‘?e''. e_unred_index (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) = SOME e''’ >- (
    DISJ2_TAC >>
    DISJ1_TAC >>
    gvs[] >>
    drule_all e_update_index_typed >>
    strip_tac >>
    imp_res_tac e_unred_index_not_const >>
    qpat_x_assum ‘!e e'. MEM e _ /\ _ ==> _’ (qspecl_then [‘EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)’, ‘e''’] mp_tac) >>
    impl_tac >- (
     gvs[]
    ) >>
    disch_then (qspecl_then [‘gscope’, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’, ‘t_tau (tau_bit w)’, ‘b''’, ‘(c0,c1,c2,c3,c4,c5,c6,c7)’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f'’, ‘Prs_n’] mp_tac) >>
    impl_tac >- (
     gvs[]
    ) >>
    strip_tac >>
    Q.EXISTS_TAC `framel` >>
    Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list ,
                   ZIP (LUPDATE (e_update_index (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) e') i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) ,
                   ZIP (MAP FST xdl,MAP SND xdl)))` >>
    Q.EXISTS_TAC `i` >>
    Q.EXISTS_TAC `e''` >>
    Q.EXISTS_TAC `e'` >>
    rw[] >> (
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP] >>
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[]
    )
   ) >>
   ‘?lval. get_lval_of_e (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) = SOME lval’ by (
    gvs[is_get_lval]
   ) >>
   (* the l-value has no stack index that is not a value either *)
   ‘lval_unred_index lval = NONE’ by (
    imp_res_tac get_lval_of_e_unred_index >>
    Cases_on ‘e_unred_index (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list))’ >> (
     gvs[]
    )
   ) >>
   (* an argument with an out-of-bounds stack index is saved with an unspecified value *)
   Cases_on ‘lval_oob (scopest ⧺ gscope) lval’ >- (
    DISJ2_TAC >>
    DISJ2_TAC >>
    imp_res_tac lval_oob_lookup_lval >>
    drule_all read_lval_exists >>
    disch_then (qspecl_then [‘c6’, ‘c7’] strip_assume_tac) >>
    Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list ,
                   ZIP (LUPDATE (e_saved (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) v) i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) ,
                   ZIP (MAP FST xdl,MAP SND xdl)))` >>
    Q.EXISTS_TAC `i` >>
    Q.EXISTS_TAC `e_saved (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) v` >>
    Q.EXISTS_TAC `i'` >>
    rw[] >> (
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP] >>
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[save_arg_oob_def]
    )
   ) >>
   DISJ1_TAC >>
   (* the l-value of the argument can be looked up *)
   qspecl_then [‘EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)’, ‘ARB’, ‘t_tau (EL i (MAP (λ(e_,tau_,x_,d_,b_). tau_) e_tau_x_d_b_list))’, ‘t_scope_list_g’, ‘gscope’, ‘t_scope_list’, ‘scopest’, ‘(order,f',delta_g,delta_b,delta_x,delta_t)’] mp_tac e_lval_WT >>
   impl_tac >- (
    gvs[]
   ) >>
   strip_tac >>
   Q.EXISTS_TAC `ZIP ( MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list ,
                  ZIP (LUPDATE (e_saved (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) v) i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list) ,
                  ZIP (MAP FST xdl,MAP SND xdl)))` >>
   Q.EXISTS_TAC `i` >>
   Q.EXISTS_TAC `e_saved (EL i (MAP (λ(e_,tau_,x_,d_,b_). e_) e_tau_x_d_b_list)) v` >>
   rw[] >| [
     rfs[map_quad_zip112]
     ,
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP]
     ,
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP] >>
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[]
     ,
     rfs[map_quad_zip112] >>
     fs[GSYM UNZIP_MAP] >>
     `MAP (λ(t,x,d). d) (MAP (λ(e_,tau_,x_,d_,b_). (tau_,x_,d_)) e_tau_x_d_b_list) =
                     (MAP (λ(e_,tau_,x_,d_,b_). d_) e_tau_x_d_b_list)` by gvs[MAP_MAP_txd] >>
     gvs[]
     ,
     rfs[map_quad_zip112] >>
     simp[save_arg_def]
     ,
     rfs[map_quad_zip112]
   ]
 ]
]

,

(****************)
(*  select      *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_select e l s)`` >>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_const e` >| [
 (* case select v l s *)
 gvs[is_const_val_exsist, clause_name_def]
 ,  
 fs[prog_exp_def] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`gscope`, `scopest`, `t_scope_list`, ` t_scope_list_g`,
   `t_tau (tau_xtl struct_ty x'_tau_list)`, ` b'`, ` c`, ` order`, `delta_g`,
   ` delta_b`, ` delta_t`, ` delta_x`,`f` , ‘Prs_n’])) >>
 gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]
]

,

(****************)
(*  struct      *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_struct l2)`` >>
gvs[] >>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

(* we need show that there can be struct reduction from
    e_struct -> e_struct if we can find an unred_mem_index  and
    e_struct -> v_struct if all the members are constants
   so we start cases on is consts
*)

Cases_on `is_consts (MAP (λ(f_,e_,tau_,b_). (e_)) f_e_tau_b_list)` >| [
 (* starting from the left disjuction
   if all members are constsants then we know that
   vl_of_el actually exists *)
   
 DISJ2_TAC >>

 fs[clause_name_def] >>
 Q.EXISTS_TAC `ZIP((MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
               ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list),
	             vl_of_el (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 rw[map_distrub]  >>
 gvs[] >>

 gvs[map_distrub] >>
 fs[GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub] >>
 gvs[map_rw2]
 
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
 (STRIP_ASSUME_TAC o (Q.SPECL
 [`gscope`,`scopest`, `t_scope_list`, `t_scope_list_g`,
 `(t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`,
 `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
 `c`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f`, ‘Prs_n’ 
 ]) o (SIMP_RULE (srw_ss()) [prog_exp_def])) >>

 gvs[] >>

 subgoal `¬is_const (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- (
 IMP_RES_TAC unred_mem_is_const >>
 gvs[]) >> gvs[] >>

 Q.EXISTS_TAC `framel` >>
 Q.EXISTS_TAC `ZIP((MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
               ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list),
	       LUPDATE e' i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 Q.EXISTS_TAC `i` >>
 Q.EXISTS_TAC `e'` >>

 rw[map_distrub]  >>
 gvs[] >>

 gvs[map_distrub] >>
 fs[GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub] >>
 gvs[map_rw2]

]

,

(****************)
(*  header      *)
(****************)

SIMP_TAC list_ss [prog_exp_def] >>
REPEAT STRIP_TAC >>

OPEN_EXP_TYP_TAC ``(e_header b l2)`` >>
gvs[] >>
gvs[is_const_def, clause_name_def] >>

RW_TAC (srw_ss()) [Once e_sem_cases] >>
rw[] >>
srw_tac [boolSimps.DNF_ss][] >>

Cases_on `is_consts (MAP (λ(f_,e_,tau_,b_). (e_)) f_e_tau_b_list)` >| [
 (* starting from the left disjuction
   if all members are constsants then we know that
   vl_of_el actually exists *)
   
 DISJ2_TAC >>

 fs[clause_name_def] >>
 Q.EXISTS_TAC `ZIP((MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
               ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list),
	             vl_of_el (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 rw[map_distrub]  >>
 gvs[] >>

 gvs[map_distrub] >>
 fs[GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub] >>
 gvs[map_rw2]
 
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
 (STRIP_ASSUME_TAC o (Q.SPECL
 [`gscope`,`scopest`, `t_scope_list`, `t_scope_list_g`,
 `(t_tau (EL i (MAP (λ(f_,e_,tau_,b_). tau_) (f_e_tau_b_list : (string # e # tau # bool) list))))`,
 `(EL i (MAP (λ(f_,e_,tau_,b_). b_) (f_e_tau_b_list : (string # e # tau # bool) list)))`,
 `c`, `order`, `delta_g`, `delta_b`, `delta_t`, `delta_x`, `f` , ‘Prs_n’
 ]) o (SIMP_RULE (srw_ss()) [prog_exp_def])) >>

 gvs[] >>

 subgoal `¬is_const (EL i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list))` >- (
 IMP_RES_TAC unred_mem_is_const >>
 gvs[]) >> gvs[] >>

 Q.EXISTS_TAC `framel` >>
 Q.EXISTS_TAC `ZIP((MAP (λ(f_,e_,tau_,b_). f_) f_e_tau_b_list),
               ZIP((MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list),
	       LUPDATE e' i (MAP (λ(f_,e_,tau_,b_). e_) f_e_tau_b_list)))` >>

 Q.EXISTS_TAC `i` >>
 Q.EXISTS_TAC `e'` >>

 rw[map_distrub]  >>
 gvs[] >>

 gvs[map_distrub] >>
 fs[GSYM UNZIP_MAP, vl_of_el_def, map_rw_quad, map_distrub] >>
 gvs[map_rw2]

]


,

(****************)
(*  saved       *)
(****************)

fs[prog_exp_def] >>
rpt strip_tac >>
SIMP_TAC (srw_ss()) [Once e_sem_cases] >>
srw_tac [boolSimps.DNF_ss][clause_name_def]

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
]
QED
