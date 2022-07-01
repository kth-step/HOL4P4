open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open blastLib bitstringLib;
open p4Theory;
(*open p4_exec_semTheory;*)
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;



(*Tactics*)

fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (gsl,[(fun,^stm_term,gam)],ctl,st) stat` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))



(*********** SAME SATE DEF *****************)

val same_state_def = Define `
 same_state (st:state) st'  =
((st = st'))
`;


(******** STMT DETERMINISIM DEF ************)

val det_stmt_def = Define `
 det_stmt stm = ! (c:ctx) (ss:scopes_stack) (s':state) (s'':state) (g_scope_list:scope list) (f:funn) status (ctrl:ctrl).
(stmt_red c ( g_scope_list , ([(f,stm,ss)]) , ctrl, status) (s'))
/\
(stmt_red c ( g_scope_list , ([(f,stm,ss)]) , ctrl, status) (s''))
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
 det_exp e = ! c scope scopest e' e'' frame frame'.
(e_red c scope scopest e e' frame )
/\
(e_red c scope scopest e e'' frame' ) 
==>
(same_frame_exp frame frame' e' e'')
`;


(********** EXPRESSION List P3 ***************)
(* Supposed to be a property that states the following:
every expression element of the list is deterministic
for clarification, check the definition of e_induction
in P4 theory, it is basically P3 *)

val det_exp_list_def = Define `
   det_exp_list (l : e list)  = !(x : e). MEM x l ==> det_exp(x)
`;


(********** STR EXPRESSION List P1 ***************)
(* Supposed to be a property that states the following:
every expression element of the list of tuples of expression
and strings is deterministic for clarification, check
the definition of e_induction in P4 theory, it is P1 *)

val det_strexp_list_def = Define `
   det_strexp_list (l : (string#e) list)
      = !  (e:e) . MEM e (SND (UNZIP l)) ==> det_exp(e)
`;


(********** STR EXPRESSION tuple P2 ***************)
(* Supposed to be a property that states the following:
A tuple of (expression, string) in the struct or header 
is deterministic. Based on e_induction this is P2 *)

val det_strexp_tuple_def = Define `
   det_strexp_tup (tup : (string#e))
      =  det_exp (SND(tup))
`;


(******** Frame list DETERMINISIM DEF *******)
val det_frame_def = Define `
 det_frame framel = ! (c:ctx) (s':state) s'' (g_scope_list:scope list) (ctrl:ctrl) status.
(stmt_red c ( g_scope_list , framel , ctrl, status) (s'))
/\
(stmt_red c ( g_scope_list , framel , ctrl, status) (s''))
==>
( same_state s' s'')
`;


(******** parser DETERMINISIM DEF ************)
val det_parser_def = Define `
 det_parser framel =
 ! (ext_map:ext_map) (func_map:func_map) (pars_map:pars_map) (s':state) s'' (g_scope_list:scope list) (ctrl:ctrl) status.
(pars_red (  ext_map ,  func_map ,  pars_map ) ( g_scope_list , framel , ctrl, status) (s'))
/\
(pars_red (  ext_map ,  func_map ,  pars_map ) ( g_scope_list , framel , ctrl, status) (s''))
==>
( same_state s' s'')
`;


(*lemmas and thms*)

(*********Reduction of vars lemmas ************)

val lemma_v_red_forall =
prove(`` ! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl   ``,
RW_TAC (srw_ss()) [Once e_red_cases]
);

(********* lookup_funn_sig_body eq ************)

val fun_body_map_EQ =
prove(`` ! funn func_map ext_map stmt (sdl') (sdl: (string # d) list).
lookup_funn_sig_body funn func_map ext_map = SOME (stmt, sdl ) /\
lookup_funn_sig      funn func_map ext_map = SOME (sdl') ==>
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
	(MAP (λ(x_,d_). (d_)) l =
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


(*Copied from p4_exec_sem_rules, remove it whenever  that file is fixed*)
Theorem index_find_length:
 !l i f j e. (INDEX_FIND i f l = SOME (j, e)) ==> (j - i < LENGTH l)
Proof
 cheat 
QED


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
	  




(*determinism proof of expressions*)

val P4_exp_det =
prove ( `` (!e. det_exp e) /\ (! l1: e list. det_exp_list l1)  /\ (!l2 : (string#e) list .  det_strexp_list l2 ) /\ ( ! tup. det_strexp_tup tup)``,
 
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
SOME (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list') ` by METIS_TAC [SOME_EL,SOME_11] >>
REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>

(**first show that the d is the same in both lists, thus the i = i'*)
REV_FULL_SIMP_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_MAP2 >>
`i = i'` by METIS_TAC [ option_case_def]>>

(*Now try to show that the EL i l is deterministic*)
REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def, det_exp_list_def] >>
PAT_ASSUM `` ∀x._``
( STRIP_ASSUME_TAC o (Q.SPECL [`(EL i (MAP (λ(e_,e'_,x_,d_). e_) (e_e'_x_d_list:(e#e#string#d)list)))` ])) >>
(*IMP_RES_TAC unred_arg_index_in_range  >> *) cheat >>
IMP_RES_TAC EL_MEM >>
FULL_SIMP_TAC list_ss [det_exp_def]  >>
RES_TAC >>
FULL_SIMP_TAC list_ss [same_frame_exp_def]>>
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
prove ( `` !stmt. det_stmt stmt ``,

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
TRY (`SOME scopes_stack' = SOME scopes_stack''` by METIS_TAC [CLOSED_PAIR_EQ] >>
fs []) >>

(*fourth subgoal*)
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
(*   stmt_declare            *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
NTAC 2 (OPEN_STMT_RED_TAC ``stmt_declare t s o'``) >>

REV_FULL_SIMP_TAC (srw_ss()) []  >>
rfs [Once same_state_def] >>
TRY (`(g_scope_list'³',scopes_stack'') = (g_scope_list'',scopes_stack')` by METIS_TAC [] >>
rfs []) >>
rw[] >>
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
OPEN_STMT_RED_TAC ``stmt_block stm`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def]
,

(*****************************)
(*   stmt_block_ip           *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_block_ip stm`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def])  >- (
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] ) >>
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] 
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
NTAC 2 (OPEN_STMT_RED_TAC ``stmt_app s e``) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
rw [] >> fs [] >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] >| [

`ctrl (s,MAP (λ(e_,mk_). e_) e_mk_list,MAP (λ(e_,mk_). mk_) e_mk_list)  =
 ctrl (s,MAP (λ(e_,mk_). e_) e_mk_list',MAP (λ(e_,mk_). mk_) e_mk_list')
`
by METIS_TAC[] >> fs []
,

ASSUME_TAC lconst_const_imp >>
RES_TAC >>
rfs []
,

rfs [] >>
ASSUME_TAC lconst_const_imp >>
RES_TAC >>
rfs []
,

`SOME i'  =
 SOME i
`
by METIS_TAC[] >> rfs [] >> rw[] >> RES_TAC >> rw[] >>
ASSUME_TAC P4_exp_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]

]

,

(*****************************)
(*   stmt_extern             *)
(*****************************)

(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ext)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_def] ) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

`SOME (g_scope_list'',scopes_stack',ctrl'') = SOME (g_scope_list'³',scopes_stack'',ctrl'³') `
by METIS_TAC [ option_case_def]>>

rw [] >> fs [] >>
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES] >>
 fs [option_case_def]
]
);






(**************************************************)
(**************************************************)
         (*determinism proof frame list*)
(**************************************************)
(**************************************************)


val P4_frame_det =
prove ( `` ! framel. det_frame framel ``,

Cases_on `framel` >>
FULL_SIMP_TAC (srw_ss()) [det_frame_def] >>
REPEAT STRIP_TAC >-
( FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] ) >>

Cases_on `t` >| [
	 (*single frame*)
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
Cases_on `h` >>
Cases_on `r` >>
RES_TAC >>
fs [same_state_def]
,
	(*list of frames*)
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases] >|[

	 (*comp1-comp1*)
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
Cases_on `h` >>
Cases_on `r` >>
RES_TAC >>
fs [] 
,
	(*comp1-comp2*)
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def] >>
rfs [notret_def]>>
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
RES_TAC >>
rfs[notret_def] >>
TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
rw[] >>
rfs[notret_def]>>
IMP_RES_TAC lemma_v_red_forall
,
	(*comp2-comp1*)
FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def, notret_def] >>
FULL_SIMP_TAC (srw_ss()) [notret_def]>>
rw[] >>
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
RES_TAC >>
rfs[notret_def] >>
TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
rw[] >>
rfs[notret_def]>>
IMP_RES_TAC lemma_v_red_forall
,
	(*comp2-comp2*)
rw[] >>
`(stmt'³',x_d_list) = (stmt'⁷',x_d_list')` by METIS_TAC [SOME_EL,SOME_11] >>
IMP_RES_TAC MAP4 >>
ASSUME_TAC P4_stmt_det >>
fs [det_stmt_def, same_state_def]  >>
RES_TAC >>
rw[] >>
`(g_scope_list'',scopes_stack'⁴') = (g_scope_list'³',scopes_stack'⁵') ` by METIS_TAC [SOME_EL,SOME_11] >>
rfs[SOME_EL,SOME_11]
]]
);


(**************************************************)
(**************************************************)
         (*determinism proof parser*)
(**************************************************)
(**************************************************)


val P4_parser_det =
prove (
`` ! framel. det_parser framel ``,
FULL_SIMP_TAC (srw_ss()) [det_parser_def, same_state_def] >>
NTAC 2 (FULL_SIMP_TAC (srw_ss()) [Once pars_red_cases]) >>
REPEAT STRIP_TAC >>
ASSUME_TAC P4_frame_det >>
fs [det_frame_def, same_state_def]  >>
RES_TAC >>
rw[] >>
rfs [Once stmt_red_cases]
);
