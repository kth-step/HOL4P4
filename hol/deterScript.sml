open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory p4_auxTheory ottTheory;
open p4_exec_semTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;

val _ = new_theory "deter";

(*Tactics*)

fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))



(*********** SAME SATE DEF *****************)

val same_state_def = Define `
 same_state (st:'a state) st'  =
(st = st')
`;


(******** STMT DETERMINISIM DEF ************)


val det_stmt_def = Define `
 det_stmt (stm) (ty:'a itself) = ! (c: 'a ctx) ascope sl s' s'' g_scope_list f status .
(stmt_red c ( ascope, g_scope_list, ([(f,[stm],sl)]), status) (s'))
/\
(stmt_red c ( ascope, g_scope_list, ([(f,[stm],sl)]), status) (s''))
==>
( same_state s' s'')
`;



(********* SAME FRAME and EXP DEF *************)

val same_frame_exp_def = Define `
 same_frame_exp (frame:frame_list) frame' (e:e) e'  =
((frame = frame') /\ (e = e'))
`;


(********** EXPRESSION DETER DEF *************)
(* Based on the e_induction definition, this is P0
wich shows that each exression reduction is determ.*)

val det_exp_def = Define `
 det_exp e (ty:'a itself) = ! (c: 'a ctx) scope scopest e' e'' frame frame'.
(e_red (c: 'a ctx) scope scopest e e' frame )
/\
(e_red (c: 'a ctx)  scope scopest e e'' frame' ) 
==>
(same_frame_exp frame frame' e' e'')
`;


(********** EXPRESSION List P3 ***************)
(* Supposed to be a property that states the following:
every expression element of the list is deterministic
for clarification, check the definition of e_induction
in P4 theory, it is basically P3 *)

val det_exp_list_def = Define `
   det_exp_list (l : e list) (ty:'a itself)  = !(x : e). MEM x l ==> det_exp (x) (ty:'a itself)
`;


(********** STR EXPRESSION List P1 ***************)
(* Supposed to be a property that states the following:
every expression element of the list of tuples of expression
and strings is deterministic for clarification, check
the definition of e_induction in P4 theory, it is P1 *)

val det_strexp_list_def = Define `
   det_strexp_list (l : (string#e) list) (ty:'a itself)
      = !  (e:e) . MEM e (SND (UNZIP l)) ==> det_exp(e) (ty:'a itself)
`;


(********** STR EXPRESSION tuple P2 ***************)
(* Supposed to be a property that states the following:
A tuple of (expression, string) in the struct or header 
is deterministic. Based on e_induction this is P2 *)

val det_strexp_tuple_def = Define ` 
   det_strexp_tup (tup : (string#e)) (ty:'a itself)
      =  det_exp (SND(tup)) (ty:'a itself)
`;


(******** stmt list DETERMINISIM DEF *******)
val det_stmtl_def = Define `
 det_stmtl stmtl (ty:'a itself) = ! (c:'a ctx) (s':'a state) s'' (g_scope_list:scope list) status (ss:scope list) (f:funn) ascope.
(stmt_red c ( ascope, g_scope_list , ([(f,stmtl,ss)]) , status) (s'))
/\
(stmt_red c ( ascope, g_scope_list , ([(f,stmtl,ss)]) , status) (s''))
==>
( same_state s' s'')
`;

(******** Single frame DETERMINISIM DEF *******)
val det_frame_def = Define `
 det_frame frame (ty:'a itself) = ! (c:'a ctx) (s':'a state) s'' (g_scope_list:scope list) status ascope.
(frames_red c ( ascope, g_scope_list , [frame] , status) (s'))
/\
(frames_red c ( ascope, g_scope_list , [frame] , status) (s''))
==>
( same_state s' s'')
`;


(******** Frame list DETERMINISIM DEF *******)
val det_framel_def = Define `
 det_framel framel (ty:'a itself) = ! (c:'a ctx) (s':'a state) s'' (g_scope_list:scope list)  status ascope.
(frames_red c ( ascope, g_scope_list , framel, status) (s'))
/\
(frames_red c ( ascope, g_scope_list , framel, status) (s''))
==>
( same_state s' s'')
`;

(*lemmas and thms*)

(*********Reduction of vars lemmas ************)

Theorem lemma_v_red_forall:
! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl
Proof
RW_TAC (srw_ss()) [Once e_red_cases]
QED


(********* lookup_funn_sig_body eq ************)

val fun_body_map_EQ =
prove(`` ! funn func_map b_func_map ext_map stmt (sdl') (sdl: (string # d) list).
lookup_funn_sig_body funn func_map b_func_map ext_map = SOME (stmt, sdl ) /\
lookup_funn_sig      funn func_map b_func_map ext_map = SOME (sdl') ==>
(sdl = sdl')
``,
REPEAT STRIP_TAC >>
rfs [lookup_funn_sig_def] 
);



(*********Mapping equv. lemmas ************)

val lemma_MAP1 =
prove (``! l l'  .
          (MAP (λ(e_,x_,d_). (x_,d_)) l =
        MAP (λ(e_,e'_,x_,d_). (x_,d_)) l') ==> 
        ((MAP (λ(e_,x_,d_). d_) l) = (MAP (λ(e_,e'_,x_,d_). d_) l')) /\
        ((MAP (λ(e_,x_,d_). x_) l) = (MAP (λ(e_,e'_,x_,d_). x_) l'))``,


Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
Cases_on `r''` >>
REV_FULL_SIMP_TAC list_ss []
);


val lemma_MAP2 =
prove (``
! l l' .
        (MAP (λ(e_,e'_,x_,d_). (x_,d_)) l =
        MAP (λ(e_,e'_,x_,d_). (x_,d_)) l') ==>
	(MAP (λ(e_,e'_,x_,d_). d_) l =
        MAP (λ(e_,e'_,x_,d_). d_) l') ``,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
Cases_on `r` >>
Cases_on `r''` >>
REV_FULL_SIMP_TAC list_ss []
);


val lemma_MAP3 =
prove ( ``
!l l' .
        (MAP (λ(e_,x_,d_). (x_,d_)) l =
        MAP (λ(e_,x_,d_). (x_,d_)) l') ==>
	(MAP (λ(e_,x_,d_). (x_)) l =
        MAP (λ(e_,x_,d_). (x_)) l') /\
	(MAP (λ(e_,x_,d_). (d_)) l =
        MAP (λ(e_,x_,d_). (d_)) l') ``,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
REV_FULL_SIMP_TAC list_ss []
);


val MAP4 =
prove ( ``
!l l' .
        ( l =  l') ==>
	(MAP (λ(x_,d_). (x_)) l =
        MAP (λ(x_,d_). (x_)) l) /\
	(MAP (λ(x_,d_). (d_)) l' =
        MAP (λ(x_,d_). (d_)) l') ``,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
REV_FULL_SIMP_TAC list_ss []
);


val lemma_MAP5 =
prove ( ``
!l l' .
        ( MAP (λ(f_,e_,e'_). (f_,e_)) l =
        MAP (λ(f_,e_,e'_). (f_,e_)) l') ==>
	(MAP (λ(f_,e_,e'_). (f_)) l =
        MAP (λ(f_,e_,e'_). (f_)) l') /\
	(MAP (λ(f_,e_,e'_). (e_)) l =
        MAP (λ(f_,e_,e'_). (e_)) l') ``,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
REV_FULL_SIMP_TAC list_ss []
);



val lemma_MAP6 =
prove ( ``
!l l'. (MAP (λ(f_,e_,e'_). f_) l = MAP (λ(f_,e_,e'_). f_) l') /\
 (MAP (λ(f_,e_,e'_). e_) l = MAP (λ(f_,e_,e'_). e_) l') /\
 (MAP (λ(f_,e_,e'_). e'_)l = MAP (λ(f_,e_,e'_). e'_) l') ==>
 MAP (λ(f_,e_,e'_). (f_,e'_)) l =
        MAP (λ(f_,e_,e'_). (f_,e'_)) l' ``,

Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>


Cases_on `h'` >>
Cases_on `r` >>
REV_FULL_SIMP_TAC list_ss [] >>
fs [ELIM_UNCURRY]
);	


val lemma_MAP7 =
prove ( ``
!l l'. MAP (λ(f_,e_,e'_). (f_,e_)) l =
        MAP (λ(f_,e_,v_). (f_,e_)) l' ==>
MAP (λ(f_,e_,e'_). (e_)) l =
        MAP (λ(f_,e_,v_). (e_)) l' ``,
Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>
Cases_on `h'` >>
Cases_on `r` >>
REV_FULL_SIMP_TAC list_ss [] >>
fs [ELIM_UNCURRY]
);



(********* lval and is_const lemmas ************)

val lemma_const_notlval =
prove (``!e. is_const e ==> ~ is_e_lval e``,
Cases_on `e` >>
EVAL_TAC
);

val lemma_lval_notconst =
prove (``!e. is_e_lval e ==> ~ is_const e``,
Cases_on `e` >>
EVAL_TAC
);

val lemma_dir_EQ =
prove (``!d. (¬is_d_out d = is_d_none_in d) /\ (is_d_out d = ¬is_d_none_in d) ``,
Cases_on `d` >>
EVAL_TAC
);



(********* Proving the mono P Q  lemmas ************)

(**************************
P is (is_d_none_in d ∧ ¬is_const e)
Q is ((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e))
show that P ==> not Q
**************************)

val dir_const_imp1 =
prove(`` ! d e.(is_d_none_in d ∧ ¬is_const e)
	     ==> ~((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e)) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
DISJ1_TAC>>
METIS_TAC[]
);


val dir_const_imp2 =
prove(``
(∀y. (λ(d,e). is_d_none_in (d) ∧ ¬is_const (e)) y ⇒
             ($¬ ∘
              (λ(d,e).
                   (is_d_none_in (d) ⇒ is_const (e)) ∧
                   (¬is_d_none_in (d) ⇒ is_e_lval (e)))) y)``,

STRIP_TAC>>
Cases_on `y`>>
FULL_SIMP_TAC std_ss [dir_const_imp1] 
);



val dir_const_imp3 =
prove(`` ! d e. ((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e))
                     ==> ~(is_d_none_in d ∧ ¬is_const e) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
METIS_TAC[]
);


val dir_const_imp4 =
prove(``
(∀y. (λ(d,e). ¬is_arg_red d e) y ⇒
             ¬(λ(d,e). is_arg_red d e) y)``,

STRIP_TAC>>
Cases_on `y`>>
FULL_SIMP_TAC std_ss [dir_const_imp1, is_arg_red_def, lemma_dir_EQ]
);


(***************************
Show that
INDEX_FIND 0 P l = SOME x ==> P(x)
****************************)

val index_some1 =
prove(``!l n. ((INDEX_FIND n (λ(d,e). is_d_none_in d ∧ ¬is_const e)
                  l) = SOME x)  ==> (λ(d,e). is_d_none_in d ∧ ¬is_const e) (SND x) ``,
Induct >| [
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
Cases_on `(λ(d,e). is_d_none_in d ∧ ¬is_const e) h` >>
RW_TAC (list_ss) [] >>
Q.PAT_X_ASSUM `∀n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`SUC n`])) >>
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
RW_TAC (list_ss) [] 
]
);


(***************************
Show that 
(INDEX_FIND n P l = NONE) = ~ EXISTS P l
****************************)

val index_some2 =
prove(``! l n. (( INDEX_FIND n (λ(d,e). is_d_none_in d ∧ ¬is_const e) l) = NONE) =
       ~(EXISTS (λ(d,e). is_d_none_in d ∧ ¬is_const e) l)``,
Induct >|[
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
Cases_on `(λ(d,e). is_d_none_in d ∧ ¬is_const e) h` >|[
FULL_SIMP_TAC list_ss [SND]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
]
]
);


(***************************
Show that for a generic P (Lemma T4)
(INDEX_FIND n P l = NONE) = ~ EXISTS P
****************************)

val index_none_not_exist =
prove(``! l  n P. (( INDEX_FIND n P l) = NONE) = ~(EXISTS (P) l)``,
Induct >|[
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
REPEAT STRIP_TAC >>
Cases_on `P h` >>
FULL_SIMP_TAC list_ss []
]
);


(***************************
Show that (equivelnt to above)
(INDEX_FIND n P l = NONE) = EVERY ~P l
Here just write P and substitute later.
****************************)

val index_none_not_every =
prove(``! l P n. (( INDEX_FIND n (P) l) = NONE) = (EVERY ($¬ ∘ P) l)``,
FULL_SIMP_TAC list_ss [NOT_EXISTS, index_none_not_exist]
);



(***************************
WE CANT SHOW THIS:
! l P n. (( INDEX_FIND n P l) = NONE) = ~(( INDEX_FIND n P l) = SOME x)
BUT WE CAN SHOW
! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x)
Here just write P and substitute later.
****************************)

val index_none_not_some =
prove(``! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x) ``,
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
);


val index_none_not_none =
prove(``! l P n. (( INDEX_FIND n P l) = SOME x) ==> ~(( INDEX_FIND n P l) = NONE) ``,
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
);

(***************************
Show that Lemma T6
(?x . INDEX_FIND n P l = SOME x) = EXISTS P l
Here just write P and substitute later.
****************************)

val not_index_none_exist =
prove(``
∀ l n P. ~ (INDEX_FIND n P l = NONE) ⇔ EXISTS P l ``,
REPEAT GEN_TAC >>
ASSUME_TAC index_none_not_exist>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF]
);


val not_index_none_some =
prove(``
∀ l n P.~ (INDEX_FIND n P l = NONE) = ? x. ( INDEX_FIND n P l) = SOME x``,
REPEAT GEN_TAC >>
Cases_on `INDEX_FIND n P l ` >>
FULL_SIMP_TAC (std_ss) [NOT_SOME_NONE,option_CLAUSES ]
);


val exists_index_some =
prove(``!  l P n. (?x .(( INDEX_FIND n P l) = SOME x)) = (EXISTS P l)``,
REPEAT GEN_TAC >>
ASSUME_TAC index_none_not_exist>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC not_index_none_exist >>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC not_index_none_some>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>

FULL_SIMP_TAC (srw_ss()) [not_index_none_some, not_index_none_exist , index_none_not_exist ]
);





(***************************
Show Lemma T2.1
! PQ . (∀x. P x ⇒ Q x) ⇒ (∃x. FI n P x) ⇒ ∃x. FI n Q x
****************************)


val P_Q_mono1 =
prove (``! P Q l. ((! (x) . (P x ==>  Q x) ) ==>
((EXISTS P l) ==>
(EXISTS Q l)))``,
REPEAT STRIP_TAC >>
ASSUME_TAC MONO_EXISTS >>
FULL_SIMP_TAC list_ss[MONO_EXISTS ]
);


val P_Q_mono2 =
prove (``
! P Q l n. ((!  (y) . (P y ==>  Q y) ) ==>
((? v. INDEX_FIND n P l = SOME v) ==>
(? v. INDEX_FIND n Q l = SOME v)))

``,
REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``P: (α -> bool)``, ``Q:(α -> bool)``, ``l:(α list)``] P_Q_mono1) >>
(*twice*)
ASSUME_TAC  exists_index_some >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `P`, `n`])) >>

ASSUME_TAC  exists_index_some >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `Q`, `n`])) >>
RES_TAC>>
fs []
);


(***************************
If a minimum index found, then the arg list is unreduced
****************************)

val lemma_args =
prove (`` ! dl el i. (unred_arg_index dl el = SOME i) ==> ~ check_args_red dl el ``,
Cases_on `dl`>>
Cases_on `el` >|[

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg [] []`>>
rfs [find_unred_arg_def, INDEX_FIND_def]
,

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg [] (h::t)`>>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg (h::t) []`>>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

SIMP_TAC (list_ss) [unred_arg_index_def]>>
REWRITE_TAC [check_args_red_def]>>
Cases_on ` find_unred_arg (h::t) (h'::t')`
>|[
REPEAT STRIP_TAC >>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

rfs [find_unred_arg_def] >>
rfs [INDEX_FIND_def, ZIP_def]>>
Cases_on `¬is_arg_red h h'`>| [
rfs [is_arg_red_def] 
,
STRIP_TAC >>
FULL_SIMP_TAC (list_ss) [] >>

ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:d#e``] P_Q_mono2) >>

Q.PAT_X_ASSUM `∀P Q l n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`λ(d,e). ¬is_arg_red d e `,
`($¬ ∘ (λ(d,e). is_arg_red d e))`,
`ZIP (t,t')`,
`1`
])) >>
FULL_SIMP_TAC std_ss [dir_const_imp4] >>

RES_TAC>>
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:d#e``] exists_index_some) >>

Q.PAT_X_ASSUM `∀l P n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`ZIP (t,t') `,
`($¬ ∘ (λ(d,e). is_arg_red d e))`,
`1`
])) >>
fs[]

]]]);



(*******list of const and const thms  **************)
val not_exist_every =
prove(``  ! el . ~(EXISTS (\e. ~(is_const e)) el) = (EVERY (\e. is_const e ) el) ``,
STRIP_TAC >>
EQ_TAC >>
REWRITE_TAC[EVERY_NOT_EXISTS]>>
fs[]
);


val lconst_every =
prove(``  ! el . is_consts el = (EVERY (\e. is_const e ) el) ``,
REWRITE_TAC[is_consts_def]>>
fs[not_exist_every]
);



val lconst_const_imp =
prove(`` !l i.  (index_not_const l = SOME i) ==> ~ is_consts l	``,
STRIP_TAC>>
FULL_SIMP_TAC std_ss [index_not_const_def, INDEX_FIND_def] >>
Cases_on `INDEX_FIND 0 (λe. ¬is_const e) l ` >>
fs[] >>
STRIP_TAC >>
rw[is_consts_def] >>
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:e``] exists_index_some) >>

Q.PAT_X_ASSUM `∀l P n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`l`,
`(λe. ¬is_const e)`,
`0`
])) >>

rfs[combinTheory.o_DEF]
);


val unred_mem_not_const =
prove(``
!l i. unred_mem_index (l) = SOME i ==> ~ is_consts (l) ``,
NTAC 3 STRIP_TAC>>
FULL_SIMP_TAC std_ss [unred_mem_index_def] >>
Cases_on `unred_mem l` >>
fs[is_consts_def, unred_mem_def] >>
IMP_RES_TAC index_none_not_none >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
IMP_RES_TAC index_none_not_none >>
IMP_RES_TAC not_index_none_exist
);

val ured_mem_length =
prove(`` !l i . (unred_mem_index l = SOME i) ==> i < LENGTH l ``,
REPEAT STRIP_TAC >>
fs[unred_mem_index_def] >>
Cases_on `unred_mem l`>>
fs[] >>
fs[unred_mem_def] >>
Cases_on `x` >>
IMP_RES_TAC index_find_length >>
fs []
);


(* Mapping, EL and MEM thms*)
val map_snd_EQ =
prove(``
!l . MAP (λx. SND x) l = MAP SND l``,
Induct >>
RW_TAC list_ss [MAP]
);


val map_fst_snd_EQ =
prove(``
!l. MAP (λx. FST (SND x)) l = (MAP SND (MAP (λx. (FST x,FST (SND x))) l)) ``,
Induct >>
RW_TAC list_ss [MAP]
);



val mem_el_map1 =
prove(`` ! l i .
MEM (EL i (MAP (λ(f_,e_). e_) l))
               (MAP (λ(f_,e_). e_) l) ==>
MEM (EL i (MAP (λ(f_,e_). e_) l))
               (SND (UNZIP (MAP (λ(f_,e_). (f_,e_)) l)))	``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [UNZIP_MAP] >>
FULL_SIMP_TAC list_ss [SND_EQ_EQUIV, SND_PAIR_MAP] >>
fs [ELIM_UNCURRY] >>
FULL_SIMP_TAC list_ss [map_snd_EQ]
);


val mem_el_map2 =
prove(`` ! l i .
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (MAP (λ(f_,e_,e'_). e_) l) ==>
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (SND (UNZIP (MAP (λ(f_,e_,e'_). (f_,e_)) l)))	``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [UNZIP_MAP] >>
FULL_SIMP_TAC list_ss [SND_EQ_EQUIV, SND_PAIR_MAP] >>
fs [ELIM_UNCURRY] >>
FULL_SIMP_TAC list_ss [map_snd_EQ, map_fst_snd_EQ] 
);
	  



val scopes_to_pass_same =
prove(``
! stmt g_scope_list g_scope_list' scopes_stack stmt_stack' ctrl funn v  (ext_map:'a ext_map) (func_map:func_map) (b_func_map:b_func_map) (pars_map:pars_map) (tbl_map:tbl_map) ascope apply_table_f. 
(SOME g_scope_list' = scopes_to_pass funn func_map b_func_map g_scope_list ) /\
(stmt_red ( apply_table_f ,  ext_map ,  func_map ,  b_func_map  ,  pars_map ,  tbl_map ) 
          (ascope, g_scope_list,[(funn,[stmt],scopes_stack)],status_running)
          (ascope, g_scope_list,[(funn,stmt_stack',scopes_stack)],
           status_returnv v)) ==>	   
(stmt_red ( apply_table_f ,  ext_map ,  func_map ,  b_func_map  ,  pars_map ,  tbl_map ) 
          (ascope, g_scope_list',[(funn,[stmt],scopes_stack)],status_running)
          (ascope, g_scope_list',[(funn,stmt_stack',scopes_stack)],
           status_returnv v)) `` ,
	   
REPEAT STRIP_TAC >>
Induct_on `stmt`  >>

REPEAT STRIP_TAC >>
rw[] >>
rfs[] >>
TRY (OPEN_STMT_RED_TAC ``stmt_seq stmt stmt'``) >>
RW_TAC (srw_ss()) [Once stmt_red_cases] >>
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases]
);





(*determinism proof of expressions*)

val P4_exp_det =
prove ( `` ! (ty:'a itself) .
(!  e .          det_exp e ty) /\
(! (l1: e list). det_exp_list l1 ty)  /\
(! (l2: (string#e) list) .  det_strexp_list l2 ty) /\
(! tup. det_strexp_tup tup ty)``,

STRIP_TAC >>
Induct >|[

(*****************************)
(*       e_v case            *)
(*****************************)
RW_TAC (srw_ss()) [same_state_def, det_exp_def, Once e_red_cases]
,

(*****************************)
(*       e_var case          *)
(*****************************)
RW_TAC (srw_ss()) [det_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def, Once e_red_cases, same_frame_exp_def] >>
METIS_TAC [option_case_def]
,

(*****************************)
(*    e_list case            *)
(*****************************)
RW_TAC (srw_ss()) [det_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [Once e_red_cases, same_frame_exp_def]
,

(*****************************)
(*     e_acc case            *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``e_acc e e'`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []) >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def]
,

(*****************************)
(*     UNOP case             *)
(*****************************)
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_unop u e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] >>

OPEN_EXP_RED_TAC ``(e_unop u e)`` >>
RW_TAC (srw_ss()) [] >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
REPEAT (IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def] )
,

(*****************************)
(*    binop case             *)
(*****************************)
(
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_binop e b e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) [] 

) >- (      (*e_binop e b e'*)

OPEN_EXP_RED_TAC ``(e_binop e b e')`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_state_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def]
) >-  (

	    (*e_binop (e_v v) b e'*)
OPEN_EXP_RED_TAC ``(e_binop (e_v v) b e')`` >>
RW_TAC (srw_ss()) []>>
IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [is_short_circuitable_def] 
) >>

(
(*e_mul case and after, use those as much as needed.*)
OPEN_EXP_RED_TAC ``(e_binop a b c)`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def, option_case_def] >>
FULL_SIMP_TAC (srw_ss()) [is_short_circuitable_def] )
,

(*****************************)
(*          e_concat         *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``e_concat e e'`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []) >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def]
,

(*****************************)
(*         e_slice           *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``e_slice e e' e''`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []) >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def]
,

(*****************************)
(*    e_func_call            *)
(*****************************) 
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_call s l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []  >| [

(*first subgoal*)
OPEN_EXP_RED_TAC ``(e_call s l)`` >>
RW_TAC (srw_ss()) [] >| [

` (stmt',MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list') =
 (stmt,MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list)
` by METIS_TAC [SOME_EL,SOME_11] >>

` (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list') =
 (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list)
` by METIS_TAC [CLOSED_PAIR_EQ] >>

IMP_RES_TAC lemma_MAP3>>
REV_FULL_SIMP_TAC (list_ss) [rich_listTheory.MAP_FST_funs, same_frame_exp_def, option_case_def] >>
REV_FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [option_case_def] >>
` SOME scope' =  SOME scope''
` by METIS_TAC [SOME_EL,SOME_11] >>
REV_FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [option_case_def]
,

REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
ASSUME_TAC fun_body_map_EQ >>
Q.PAT_X_ASSUM `∀funn func_map ext_map stmt sdl' sdl. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`f`,
`func_map`,
`b_func_map`,
`ext_map` ,
`stmt` ,
`MAP (λ(e_,e'_,x_,d_). (x_,d_)) (e_e'_x_d_list:(e#e#string#d)list)`,
`MAP (λ(e_,x_,d_). (x_,d_)) (e_x_d_list:(e#string#d)list)` ])) >>
rfs [] >>

IMP_RES_TAC lemma_MAP1>>
RES_TAC >>	
IMP_RES_TAC lemma_args >>
METIS_TAC[]
]

,
(*second subgoal*)

OPEN_EXP_RED_TAC ``(e_call s l)`` >>
RW_TAC (srw_ss()) [] >|[

REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
ASSUME_TAC fun_body_map_EQ >>

Q.PAT_X_ASSUM `∀funn func_map ext_map stmt sdl' sdl. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`f`,
`func_map`,
`b_func_map`,
`ext_map` ,
`stmt` ,
`MAP (λ(e_,e'_,x_,d_). (x_,d_)) (e_e'_x_d_list:(e#e#string#d)list)`,
`MAP (λ(e_,x_,d_). (x_,d_)) (e_x_d_list:(e#string#d)list)` ])) >>
rfs [] >>

IMP_RES_TAC lemma_MAP1>>
RES_TAC >>	
IMP_RES_TAC lemma_args >>
METIS_TAC[]
,

(*start the forth sub poof here*)
`SOME (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list) =
SOME (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list') ` by METIS_TAC [SOME_EL,SOME_11] >> rw[] >>
(*REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >> *)

(**first show that the d is the same in both lists, thus the i = i'*)
REV_FULL_SIMP_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_MAP2 >>
`i = i'` by METIS_TAC [ option_case_def]>> rw[] >> rfs[] >>

(*Now try to show that the EL i l is deterministic*)
REV_FULL_SIMP_TAC (srw_ss()) [det_exp_list_def] >>
PAT_ASSUM `` ∀x._``
( STRIP_ASSUME_TAC o (Q.SPECL [`(EL i (MAP (λ(e_,e'_,x_,d_). e_) (e_e'_x_d_list:(e#e#string#d)list)))` ])) >>
rw[]>>
IMP_RES_TAC unred_arg_index_in_range >>
IMP_RES_TAC EL_MEM >> rfs[]>>
FULL_SIMP_TAC list_ss [det_exp_def]  >>
RES_TAC >> rw[] >>
FULL_SIMP_TAC list_ss [same_frame_exp_def]>> rfs[] >>
rw[] >> rw[]
]  ]
,

(*****************************)
(*   e_select                *)
(*****************************)
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

(*first + second + beginning of third subgoal*)
 (OPEN_EXP_RED_TAC ``(e_select e l s)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
IMP_RES_TAC lemma_v_red_forall) >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def]>>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def, Once same_frame_exp_def ] 
,

(*****************************)
(*   e_struct                *)
(*****************************)

NTAC 2 (SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_struct l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >>
fs[] >> rw[]  >| [

(*first subgoal *)
IMP_RES_TAC lemma_MAP5 >>
fs[SOME_EL,SOME_11] >>
rw[] >>
REV_FULL_SIMP_TAC (srw_ss()) [det_strexp_list_def] >>
PAT_ASSUM `` ∀e._``
( STRIP_ASSUME_TAC o (Q.SPECL [`EL i (MAP (λ(f_,e_,e'_). (e_:e)) (f_e_e'_list':(string # e # e) list))`])) >>

IMP_RES_TAC ured_mem_length >>
IMP_RES_TAC EL_MEM >>
IMP_RES_TAC  mem_el_map2 >>
FULL_SIMP_TAC list_ss [] >>

IMP_RES_TAC det_exp_def >>
fs[same_frame_exp_def] >>

` MAP (λ(f_,e_,e'_). e'_) f_e_e'_list =
 MAP (λ(f_,e_,e'_). e'_) f_e_e'_list'
` by METIS_TAC [SOME_EL,SOME_11] >>
fs[ lemma_MAP6] 
,

(*second subgoal *)
IMP_RES_TAC unred_mem_not_const >>
IMP_RES_TAC lemma_MAP7 >>
fs[]
,

(*third subgoal *)
IMP_RES_TAC unred_mem_not_const >>
IMP_RES_TAC lemma_MAP7 >>
fs[]

,
(*fourth subgoal *)
IMP_RES_TAC lemma_MAP5 >>
rw[] >>
FULL_SIMP_TAC list_ss [] >>
` MAP (λ(f_,e_,v_). v_) f_e_v_list =
 MAP (λ(f_,e_,v_). v_) f_e_v_list'
` by METIS_TAC [SOME_EL,SOME_11] >>
IMP_RES_TAC lemma_MAP6 >>
fs[same_frame_exp_def] 
]
,

(*****************************)
(*   e_header                *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_header b l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >>
fs[] >> rw[]  >| [

(*first subgoal *)
IMP_RES_TAC lemma_MAP5 >>
fs[SOME_EL,SOME_11] >>
rw[] >>
REV_FULL_SIMP_TAC (srw_ss()) [det_strexp_list_def] >>
PAT_ASSUM `` ∀e._``
( STRIP_ASSUME_TAC o (Q.SPECL [`EL i (MAP (λ(f_,e_,e'_). (e_:e)) (f_e_e'_list':(string # e # e) list))`])) >>

IMP_RES_TAC ured_mem_length >>
IMP_RES_TAC EL_MEM >>
IMP_RES_TAC  mem_el_map2 >>
FULL_SIMP_TAC list_ss [] >>

IMP_RES_TAC det_exp_def >>
fs[same_frame_exp_def] >>

` MAP (λ(f_,e_,e'_). e'_) f_e_e'_list =
 MAP (λ(f_,e_,e'_). e'_) f_e_e'_list'
` by METIS_TAC [SOME_EL,SOME_11] >>
fs[ lemma_MAP6] 
,
IMP_RES_TAC unred_mem_not_const >>
IMP_RES_TAC lemma_MAP7 >>
fs[]
,
IMP_RES_TAC unred_mem_not_const >>
IMP_RES_TAC lemma_MAP7 >>
fs[]
,
IMP_RES_TAC lemma_MAP5 >>
rw[] >>
FULL_SIMP_TAC list_ss [] >>
` MAP (λ(f_,e_,v_). v_) f_e_v_list =
 MAP (λ(f_,e_,v_). v_) f_e_v_list'
` by METIS_TAC [SOME_EL,SOME_11] >>
IMP_RES_TAC lemma_MAP6 >>
fs[same_frame_exp_def] 
]
,

(*****************************)
(*   strexcp   []            *)
(*****************************)
FULL_SIMP_TAC list_ss [det_strexp_list_def]
,

(*****************************)
(*   strexcp   l             *)
(*****************************)
Cases_on `tup` >>
FULL_SIMP_TAC list_ss [det_strexp_tuple_def ] >>
FULL_SIMP_TAC list_ss [det_strexp_list_def] >>
FULL_SIMP_TAC list_ss [det_exp_def ] >>
NTAC 2 STRIP_TAC >|[

(*first case*)
REPEAT STRIP_TAC >>
rw [] >>
PAT_ASSUM `` ∀c scope scopest e' e'' frame frame'.
          e_red c scope scopest e e' frame ∧
          e_red c scope scopest e e'' frame' ⇒
          same_frame_exp frame frame' e' e''``
( STRIP_ASSUME_TAC o (Q.SPECL [`c`, `scope`, `scopest`, `e'`, `e''`, `frame`, `frame'`])) >>
FULL_SIMP_TAC list_ss [same_frame_exp_def]
,

(*second case*)
REPEAT STRIP_TAC >>
rw [] >>

PAT_ASSUM `` ∀e. MEM e (SND (UNZIP l2)) ⇒
            ∀c scope scopest e' e'' frame frame'.
              e_red c scope scopest e e' frame ∧
              e_red c scope scopest e e'' frame' ⇒
              same_frame_exp frame frame' e' e''``
( STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
PAT_ASSUM `` ∀c scope scopest e' e'' frame frame'.
          e_red c scope scopest e e' frame ∧
          e_red c scope scopest e e'' frame' ⇒
          same_frame_exp frame frame' e' e''``
( STRIP_ASSUME_TAC o (Q.SPECL [`c`, `scope`, `scopest`, `e'`, `e''`, `frame`, `frame'`])) >>
FULL_SIMP_TAC list_ss [same_frame_exp_def]

]
,

(*****************************)
(*   str_exp_tup             *)
(*****************************)
FULL_SIMP_TAC list_ss [det_strexp_tuple_def ]
,

(*****************************)
(*   P2       []             *)
(*****************************)
FULL_SIMP_TAC list_ss [det_exp_list_def]
,

(*****************************)
(*   P2       l              *)
(*****************************)
FULL_SIMP_TAC list_ss [det_exp_list_def] >>
REPEAT STRIP_TAC >>
rw []
]
);




(**************************************************)
(**************************************************)
      (*determinism proof single frame stmt       *)
(**************************************************)
(**************************************************)

val P4_stmt_det =
prove ( `` !stmt ty. det_stmt stmt ty``,


Induct >|[

(*****************************)
(*   stmt_empty              *)
(*****************************)
RW_TAC (srw_ss()) [same_state_def, det_stmt_def, Once e_red_cases] >>
OPEN_STMT_RED_TAC ``stmt_empty`` >>
fs []
,

(*****************************)
(*   stmt_ass                *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
NTAC 2 (OPEN_STMT_RED_TAC ``(stmt_ass l e)``) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

(*first + second + third subgoal*)
RW_TAC (srw_ss()) [assign_def, same_state_def]>>
IMP_RES_TAC lemma_v_red_forall >>
TRY (`SOME scopes_list' = SOME scopes_list''` by METIS_TAC [CLOSED_PAIR_EQ] >>
fs []) >>
rw[] >> rfs[] >>

(*fourth subgoal*)


rfs[] >>
Cases_on `assign (sl ⧺ g_scope_list) v l` >>
fs[] >>
Cases_on `separate x` >>
rw[] >>


ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]

,

(*****************************)
(*   stmt_cond               *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
NTAC 2 (OPEN_STMT_RED_TAC ``stmt_cond e stm stm'`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >>

FULL_SIMP_TAC (srw_ss()) [Once same_state_def]>>
IMP_RES_TAC lemma_v_red_forall>>
ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]
,

(*****************************)
(*   stmt_block              *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_block l stm`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]
 
,

(*****************************)
(*   stmt_ret                *)
(*****************************)
(NTAC 2 ( SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ret e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] ) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]) >>

FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] >>
IMP_RES_TAC lemma_v_red_forall>>

ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]
,

(*****************************)
(*   stmt_seq                *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_seq stm stm')`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]) >>
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def, Once same_frame_exp_def ] >>
OPEN_STMT_RED_TAC ``stmt_empty`` >>
REV_FULL_SIMP_TAC (srw_ss()) []
,

(*****************************)
(*   stmt_verify             *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_verify e e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def]>>
ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]
,

(*****************************)
(*   stmt_trans              *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_trans e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def] >>
ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]
,

(*****************************)
(*   stmt_app                *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
NTAC 2 (OPEN_STMT_RED_TAC ``stmt_app s l``) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
rw [] >> fs [] >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] >>

ASSUME_TAC lconst_const_imp >>
RES_TAC >>
rfs [] >>

`SOME i'  =
 SOME i
`
by METIS_TAC[] >> rfs [] >> rw[] >> RES_TAC >> rw[] >>
ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]


,

(*****************************)
(*   stmt_extern             *)
(*****************************)

(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ext)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] ) >>
rw[] >>
Cases_on `lookup_ext_fun f ext_map` >>
rw[] >>
Cases_on `ext_fun (ascope,g_scope_list,sl)`>>
rw[] 
]
);


(**************************************************)
(**************************************************)
         (*determinism proof statement list*)
(**************************************************)
(**************************************************)

val P4_stmtl_det =
prove ( `` ! stmtl ty. det_stmtl stmtl ty ``,

Cases_on `stmtl` >| [
FULL_SIMP_TAC (srw_ss()) [det_stmtl_def] >>
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases]
,

FULL_SIMP_TAC (srw_ss()) [det_stmtl_def] >>
REPEAT STRIP_TAC >>
Cases_on `t` >| [
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
RES_TAC >>
fs []
,
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >> fs [same_state_def] >>
rw[] >>
ASSUME_TAC P4_stmt_det >>
rfs [det_stmt_def, same_state_def]  >>

TRY (PAT_ASSUM `` ∀stmt._``
( STRIP_ASSUME_TAC o (Q.SPECL [`h`,
`(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)`,
`ascope`,
`ss`,
`(ascope'³',g_scope_list'³',
           frame_list'' ⧺ [(f,stmt_stack'',scope_list'')],status'³')`,
`(ascope'',g_scope_list'',
           frame_list' ⧺ [(f,stmt_stack',scope_list')],status'')`,
`g_scope_list`,
`f`,
`status`
])) >>
RES_TAC >>
fs [])
]]
);





val ret_lemma1a =
prove(``
! e v c g_scope_list funn scopes_stack ctrl stmt' ascope.
stmt_red c
          (ascope, g_scope_list,[(funn,[stmt_ret e],scopes_stack)],
           status_running)
          (ascope, g_scope_list,[(funn,[stmt'],scopes_stack)],status_returnv v) ==> (e = e_v v) ``,

FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] 

);


val ret_lemma1b =
prove(``
! e v c g_scope_list funn scopes_stack scopes_stack' stmt' ascope.
stmt_red c
          (ascope, g_scope_list,[(funn,[stmt_ret e],scopes_stack)],
           status_running)
          (ascope, g_scope_list,[(funn,[stmt'],scopes_stack')],status_returnv v) ==> (e = e_v v /\ scopes_stack = scopes_stack')  ``,

FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] 
);



val ret_lemma1c =
prove(``
! e v c g_scope_list g_scope_list' funn scopes_stack scopes_stack' stmt' ascope.
stmt_red c
          (ascope, g_scope_list,[(funn,[stmt_ret e],scopes_stack)],
           status_running)
          (ascope, g_scope_list',[(funn,[stmt'],scopes_stack')],status_returnv v) ==> (e = e_v v /\ scopes_stack = scopes_stack' /\ g_scope_list = g_scope_list')  ``,

FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] 
);




val ret_lemma1d =
prove(``
! e v c g_scope_list g_scope_list' funn scopes_stack scopes_stack' stmt' ascope.
stmt_red c
          (ascope, g_scope_list,[(funn,[stmt_ret e],scopes_stack)],
           status_running)
          (ascope, g_scope_list',[(funn,[stmt'],scopes_stack')],status_returnv v) ==> (e = e_v v /\ scopes_stack = scopes_stack' /\ g_scope_list = g_scope_list')  ``,

FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] 
);








val ret_lemma2a =
prove(``
! c g_scope_list g_scope_list' funn stmt stmt'   scopes_stack frame_list  ascope v .
(stmt_red c
          (ascope, g_scope_list,[(funn,[stmt],scopes_stack)],status_running)
          (ascope, g_scope_list,[(funn,[stmt'],scopes_stack)],status_returnv v))
	      ==>
((((stmt = stmt_ret (e_v v)) )  \/  ? stmt'' stmt'''. stmt = stmt_seq (stmt'') (stmt'''))) ``
,
Induct_on `stmt` >>
rw[] >> rfs[] >>
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases]
);


val not_ret_status  =
prove(``
! c g_scope_list g_scope_list' f stmt stmt' ss frame_list  ctrl  ctrl' v ascope.
~ stmt_red c
          (ascope, g_scope_list,[(f,[stmt_ret (e_v v)],ss)], status_running)
          (ascope, g_scope_list', frame_list,status_running)``
,
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >>
rw[] >>
rfs[lemma_v_red_forall]
);


val is_ret_status  =
prove(``
! c g_scope_list g_scope_list' f stmt stmt' ss frame_list  ctrl  ctrl' v status ascope.
stmt_red c
          (ascope, g_scope_list,[(f,[stmt_ret (e_v v)],ss)], status_running)
          (ascope, g_scope_list', frame_list,status) ==>  (status = status_returnv v)``
,
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >>
rw[] >>
rfs[lemma_v_red_forall]
);




val not_trans_status  =
prove(``
! c g_scope_list g_scope_list' f stmt stmt' ss frame_list v v' ascope.
~ stmt_red c
          (ascope, g_scope_list,[(f,[stmt_trans (e_v (v_str v'))],ss)], status_running)
          (ascope, g_scope_list', frame_list,status_returnv v)
``
,
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >>
rw[] >>
rfs[lemma_v_red_forall]
);



(*
We can never reach the status error... shall we remove it?
*)


val not_trans_status  =
prove(``
! c g_scope_list g_scope_list' f stmt stmt' ss frame_list  v v' ascope.
~ stmt_red c
          (ascope, g_scope_list,[(f,[stmt_trans (e_v (v_str v'))],ss)], status_running)
          (ascope, g_scope_list', frame_list,status_returnv v)
``
,
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >>
rw[] >>
rfs[lemma_v_red_forall]
);




val not_ret_run_is_trans_or_error  =
prove(``
! status.
status ≠ status_running /\ notret status ==> ((?v. status = status_trans v)) ``
,
Cases_on `status` >>
rw [notret_def] 
);



(**************************************************)
(**************************************************)
         (*determinism proof frame list*)
(**************************************************)
(**************************************************)

val P4_frame_det =
prove ( `` ! frame ty. det_frame frame ty ``,
Cases_on `frame` >>
Cases_on `r`>>
Cases_on `q'` >| [
FULL_SIMP_TAC (srw_ss()) [det_frame_def] >>
FULL_SIMP_TAC (srw_ss()) [Once frames_red_cases, same_state_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def]
,

 FULL_SIMP_TAC (srw_ss()) [det_frame_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [Once frames_red_cases] >>
  rw[] >>
  Cases_on `scopes_to_pass q func_map b_func_map g_scope_list` >>
  rw[] >>
  ASSUME_TAC P4_stmtl_det >>
  fs [det_stmtl_def]  >>
   rfs[same_state_def] >>
   RES_TAC >>
     fs []  >>
   ` g_scope_list''' =  g_scope_list'⁵'` by METIS_TAC [SOME_EL,SOME_11]
]

);








val P4_framel_det =
prove ( `` ! framel ty. det_framel framel ty``,

Cases_on `framel` >| [

(* empty frame [] *)
fs [det_framel_def, Once frames_red_cases] 
,
Cases_on `t` >| [

  (*single frame  [h] *)
  rw[det_framel_def] >>
  ASSUME_TAC P4_frame_det >>
  fs [det_frame_def, det_framel_def]  >>
  RES_TAC
,

	 (*multiple frame  h::h'::t' *)
  FULL_SIMP_TAC (srw_ss()) [det_framel_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [Once frames_red_cases] >>
  rw[] >| [
       (*comp1-comp1*)
    rw[] >>
    Cases_on `scopes_to_pass funn func_map b_func_map g_scope_list`>>
    rw[] >>

    ASSUME_TAC P4_stmtl_det >>
    fs [det_stmtl_def]  >>

    rfs[same_state_def] >>
    RES_TAC >>    rw[] >>
    ` g_scope_list''' =  g_scope_list'⁵'` by METIS_TAC [SOME_EL,SOME_11]
       ,

       (*************)
       (*comp1-comp2*)
       (*************)       

    FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def] >>
    rfs [notret_def]>>
    ASSUME_TAC P4_stmt_det >>
    fs [det_stmt_def, same_state_def]  >>
    RES_TAC >>
    rfs[notret_def] >>
    TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
    rw[] >>
    rfs[notret_def]>>
    IMP_RES_TAC lemma_v_red_forall >>
    rw[] >| [
    (*comp1+seq1 -  comp2-seq3*)
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >>
    RES_TAC >>rw[]
    ,
    (*comp1+seq3 -  comp2
    show that the transition status can only happen with stmt transition
    *)
    IMP_RES_TAC not_ret_run_is_trans_or_error >>
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >>
    RES_TAC >>rw[]
    ,
    (* comp1 - comp2 - exec*)
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    Cases_on `status''` >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >> RES_TAC >>
    rw[] >>
    rfs[notret_def] >>
    IMP_RES_TAC not_ret_status
    ]


       ,

       (*************)
       (*comp2-comp1*)
       (*************)       


    FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def] >>
    rfs [notret_def]>>
    ASSUME_TAC P4_stmt_det >>
    fs [det_stmt_def, same_state_def]  >>
    RES_TAC >>
    rfs[notret_def] >>
    TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
    rw[] >>
    rfs[notret_def]>>
    IMP_RES_TAC lemma_v_red_forall >>
          rw[] >| [
    (*comp1+seq1 -  comp2-seq3*)
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >>
    RES_TAC >>rw[]
    ,
    (*comp1+seq3 -  comp2
    show that the transition status can only happen with stmt transition
    *)
    IMP_RES_TAC not_ret_run_is_trans_or_error >>
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >>
    RES_TAC >>rw[]
    ,
    (* comp1 - comp2 - exec*)
    rw[] >> IMP_RES_TAC scopes_to_pass_same >>
    Cases_on `status''` >>
    ASSUME_TAC   P4_stmtl_det   >>
    fs[det_stmtl_def] >> RES_TAC >>
    rw[] >>
    rfs[notret_def] >>
    IMP_RES_TAC not_ret_status
    ]

       ,
       (*************)
       (*comp2-comp2*)
       (*************)

rw[] >>
(*fs [same_state_def]  >>*)
Cases_on `lookup_funn_sig_body funn func_map b_func_map ext_map` >> rw[]>>
rfs[] >>
IMP_RES_TAC MAP4 >>
rfs[] >>
ASSUME_TAC P4_stmtl_det >>
fs [det_stmtl_def]  >>
RES_TAC >>
Cases_on `assign g_scope_list v (lval_varname (varn_star funn))`    >> rw[] >>
Cases_on `scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list''` >> rw[] >>
REPEAT (Cases_on `copyout (MAP (λ(x_,d_). x_) x_d_list) (MAP (λ(x_,d_). d_) x_d_list)
          g_scope_list'⁴' scope_list' scope_list` >> rw[same_state_def] >> rfs[] >> fs [same_state_def])
  ]
  
]]);




val _ = export_theory ();

