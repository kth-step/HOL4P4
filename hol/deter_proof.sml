open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open blastLib bitstringLib;
open p4Theory;
open p4_exec_semTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;





(**************************************************)
(**************************************************)

          (*determinism proof*)

(**************************************************)
(**************************************************)




(******** SAME SATE and STMT DEF ************)
val same_state_stmt_def = Define `
 same_state_stmt (st:state) st'  =
((st = st'))
`;


(******** STMT DETERMINISIM DEF ************)
val det_stmt_def = Define `
 det_stmt stm = ! (c:ctx) (ss:scopes_stack) (s':state) (s'':state) (g_scope_list:scope list) (f:funn) status (ctrl:ctrl).
(stmt_red c ( g_scope_list , ([(f,stm,ss)]) , ctrl, status) (s'))
/\
(stmt_red c ( g_scope_list , ([(f,stm,ss)]) , ctrl, status) (s''))
==>
( same_state_stmt s' s'')
`;


(******** SAME FRAME and EXP DEF ************)
val same_frame_exp_def = Define `
 same_frame_exp (frame:frame_list) frame' (e:e) e'  =
((frame = frame') /\ (e = e'))
`;


(******** EXPRESSION DETER DEF ************)

val det_exp_def = Define `
 det_exp e = ! c scope scopest e' e'' frame frame'.
(e_red c scope scopest e e' frame )
/\
(e_red c scope scopest e e'' frame' ) 
==>
(same_frame_exp frame frame' e' e'')
`;



(******** EXPRESSION List P2 ************)
(*A supposed to be a property that states : every expression  element of the list is deterministic *)
val det_exp_list_def = Define `
   det_exp_list (l : e list)  = !(x : e). MEM x l ==> det_exp(x)
`;



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
prove(``
! (l1: (e#string#d) list) l2 . ( MAP (λ(e_,x_,d_). (x_,d_)) l1 ) = ( MAP (λ(e_,x_,d_). (x_,d_)) l2 ) ==>
(? (le1 : e list)  (lx1 : string list)  (ld1 : d list) (le2 : e list) lx2 ld2.
 MAP (λ(e_,x_,d_). (x_,d_)) (ZIP (le1, ZIP(lx1, ld1))) =
 MAP (λ(e_,x_,d_). (x_,d_)) (ZIP (le2, ZIP(lx2, ld2)))  /\ le1 = le2 /\ lx1 = lx2 /\ ld1 = ld2 ) ``,

REPEAT STRIP_TAC >>
NTAC 2 (EXISTS_TAC``[]: e list`` >>
EXISTS_TAC``[]: x list`` >>
EXISTS_TAC``[]: d list`` ) >>
FULL_SIMP_TAC list_ss []
);

val lemma_MAP2 =
prove (``!l. MAP (λ(e_,x_,d_). (x_,d_)) l = MAP SND l``,

Induct_on `l` >>
FULL_SIMP_TAC list_ss [] >>
STRIP_TAC >>
Cases_on `h` >>
Cases_on `r` >>
FULL_SIMP_TAC list_ss [] 
);

val lemma_MAP3 =
prove(`` !(l: (e#string#d) list) l' . (MAP (λ(e_ : e ,x_,d_). (x_,d_)) l = MAP (λ(e_,x_,d_). (x_,d_)) l') ==>
MAP SND l = MAP SND l'``,
FULL_SIMP_TAC list_ss [lemma_MAP2] 
);



val lemma_MAP4 =
prove(`` !(l: (e#string#d) list) l' . (MAP (λ(e_ : e ,x_,d_). (x_,d_)) l = MAP (λ(e_,x_,d_). (x_,d_)) l') /\
(MAP FST l = MAP FST l') ==>
(l = l')  ``,
FULL_SIMP_TAC list_ss [lemma_MAP2, lemma_MAP1, lemma_MAP3] >>
RW_TAC list_ss [PAIR_FST_SND_EQ,LIST_EQ_MAP_PAIR] 

);


val lemma_MAP5 =
prove (``!(l: (e#string#d) list) (l': (e#e#string#d) list)  .
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



val lemma_MAP6 =
prove (``
!(e_e'_x_d_list: (e#e#string#d) list) (e_e'_x_d_list': (e#e#string#d) list) .
        (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list =
        MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list') ==>
	(MAP (λ(e_,e'_,x_,d_). d_) e_e'_x_d_list =
        MAP (λ(e_,e'_,x_,d_). d_) e_e'_x_d_list') ``,

Induct_on `e_e'_x_d_list` >>
Induct_on `e_e'_x_d_list'` >>
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






val lemma_MAP7 =
prove ( ``
!(e_x_d_list: (e#string#d) list) (e_x_d_list': (e#string#d) list) .
        (MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list =
        MAP (λ(e_,x_,d_). (x_,d_)) e_x_d_list') ==>
	(MAP (λ(e_,x_,d_). (x_)) e_x_d_list =
        MAP (λ(e_,x_,d_). (x_)) e_x_d_list') /\
	(MAP (λ(e_,x_,d_). (d_)) e_x_d_list =
        MAP (λ(e_,x_,d_). (d_)) e_x_d_list') ``,

Induct_on `e_x_d_list` >>
Induct_on `e_x_d_list'` >>
FULL_SIMP_TAC list_ss [] >>
NTAC 3 STRIP_TAC>>

Cases_on `h` >>
Cases_on `h'` >>
Cases_on `r` >>
Cases_on `r'` >>
REV_FULL_SIMP_TAC list_ss []
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

val lemma_dc1a =
prove(`` ! d e.(is_d_none_in d ∧ ¬is_const e)
	     ==> ~((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e)) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
DISJ1_TAC>>
METIS_TAC[]
);


val lemma_dc1b =
prove(``
(∀y. (λ(d,e). is_d_none_in (d) ∧ ¬is_const (e)) y ⇒
             ($¬ ∘
              (λ(d,e).
                   (is_d_none_in (d) ⇒ is_const (e)) ∧
                   (¬is_d_none_in (d) ⇒ is_e_lval (e)))) y)``,

STRIP_TAC>>
Cases_on `y`>>
FULL_SIMP_TAC std_ss [lemma_dc1a] 
);



val lemma_dc1c =
prove(`` ! d e. ((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e))
                     ==> ~(is_d_none_in d ∧ ¬is_const e) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
METIS_TAC[]
);


(***************************
Show that
INDEX_FIND 0 P l = SOME x ==> P(x)

****************************)
val lemma_dc2 =
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

val lemma_dc3 =
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

val lemma_dc4 =
prove(``!  (l: (d#e) list) n P. (( INDEX_FIND n P l) = NONE) = ~(EXISTS (P) l)``,
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

val lemma_dc5 =
prove(``! l P n. (( INDEX_FIND n (P: (d#e -> bool)) l) = NONE) = (EVERY ($¬ ∘ P) l)``,
FULL_SIMP_TAC list_ss [NOT_EXISTS, lemma_dc4]
);



(***************************
WE CANT SHOW THIS:
! l P n. (( INDEX_FIND n P l) = NONE) = ~(( INDEX_FIND n P l) = SOME x)
BUT WE CAN SHOW
! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x)
Here just write P and substitute later.
****************************)

val lemma_dc6a =
prove(``! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x) ``,
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
);


val lemma_dc6b =
prove(``! l P n. (( INDEX_FIND n P l) = SOME x) ==> ~(( INDEX_FIND n P l) = NONE) ``,
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
);

(***************************
Show that Lemma T6
(?x . INDEX_FIND n P l = SOME x) = EXISTS P l
Here just write P and substitute later.
****************************)

val lemma_dc7a =
prove(``
∀ (l: (d#e) list) n P. ~ (INDEX_FIND n P l = NONE) ⇔ EXISTS P l ``,
REPEAT GEN_TAC >>
ASSUME_TAC lemma_dc4>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF]
);



val lemma_dc7b =
prove(``
∀ (l: (d#e) list) n P.~ (INDEX_FIND n P l = NONE) = ? x. ( INDEX_FIND n P l) = SOME x``,
REPEAT GEN_TAC >>
Cases_on `INDEX_FIND n P l ` >>
FULL_SIMP_TAC (std_ss) [NOT_SOME_NONE,option_CLAUSES ]
);



(*This is the ONE!!!!*)

val lemma_dc7c =
prove(``!  (l: (d#e) list) P n. (?x .(( INDEX_FIND n P l) = SOME x)) = (EXISTS P l)``,
REPEAT GEN_TAC >>
ASSUME_TAC lemma_dc4>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC lemma_dc7a >>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC lemma_dc7b>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>

FULL_SIMP_TAC (srw_ss()) [lemma_dc7b, lemma_dc7a , lemma_dc4 ]
);





(***************************
Show Lemma T2.1
! PQ . (∀x. P x ⇒ Q x) ⇒ (∃x. FI n P x) ⇒ ∃x. FI n Q x
****************************)


val lemma_dc_mono1 =
prove (``! P Q l. ((! (x) . (P x ==>  Q x) ) ==>
((EXISTS P l) ==>
(EXISTS Q l)))``,
REPEAT STRIP_TAC >>
ASSUME_TAC MONO_EXISTS >>
FULL_SIMP_TAC list_ss[MONO_EXISTS ]
);

val lemma_dc_mono2 =
prove (``
! P Q l n. ((!  (y : (d#e)) . (P y ==>  Q y) ) ==>
((? v. INDEX_FIND n P l = SOME v) ==>
(? v. INDEX_FIND n Q l = SOME v)))

``,
REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``P:(d # e) -> bool``, ``Q:(d # e) -> bool``, ``l:(d # e) list``] lemma_dc_mono1) >>
(*twice*)
ASSUME_TAC  lemma_dc7c >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `P`, `n`])) >>

ASSUME_TAC  lemma_dc7c >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `Q`, `n`])) >>
RES_TAC>>
fs []
);





(***************************
The Big lemma
****************************)

val lemma_args1 =
prove (`` ! dl el i. (unred_arg_index dl el = SOME i) ==> ~ check_args_red dl el ``,
Cases_on `dl`>>
Cases_on `el` >|[
RW_TAC (srw_ss()) [unred_arg_index_def]>>
RW_TAC (srw_ss()) [check_args_red_def]>>
Cases_on ` find_unred_arg [] []`>>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def] 

,
RW_TAC (srw_ss()) [unred_arg_index_def]>>
RW_TAC (srw_ss()) [check_args_red_def]>>
Cases_on ` find_unred_arg [] (h::t)`>>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def] 
,
RW_TAC (srw_ss()) [unred_arg_index_def]>>
RW_TAC (srw_ss()) [check_args_red_def]>>
Cases_on ` find_unred_arg (h::t) []`>>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def] 
,

SIMP_TAC (list_ss) [unred_arg_index_def]>>
REWRITE_TAC [check_args_red_def]>>
Cases_on ` find_unred_arg (h::t) (h'::t')`
>|[
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def]
,

FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def]>>

Cases_on `(¬is_d_out h ∧ ¬is_const h')` >| [
FULL_SIMP_TAC (list_ss) [is_arg_red_def] 
,
STRIP_TAC >>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def]>>
FULL_SIMP_TAC (list_ss) [is_arg_red_def]>>
STRIP_TAC >>
DISJ2_TAC>>
FULL_SIMP_TAC (list_ss) [lemma_dir_EQ]>>

ASSUME_TAC lemma_dc_mono2 >>
Q.PAT_X_ASSUM `∀P Q l n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`(λ(d,e). is_d_none_in d ∧ ¬is_const e) `,
`$¬ ∘ (λ(d,e). ((is_d_none_in d ⇒ is_const e) ∧
                (¬is_d_none_in d ⇒ is_e_lval e)))`,
`ZIP (t,t')`,
`1`
])) >>
FULL_SIMP_TAC std_ss [lemma_dc1b] >>

RES_TAC>>
ASSUME_TAC lemma_dc7c>>

Q.PAT_X_ASSUM `∀l P n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`ZIP (t,t') `,
`$¬ ∘ (λ(d,e). ((is_d_none_in d ⇒ is_const e) ∧
                (¬is_d_none_in d ⇒ is_e_lval e)))`,
`1`
])) >>
fs[]

]]]);




(*Tactics*)

fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))


fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red c (state_P4 Gs [(f,^stm_term ,ctrl,ss)] st) state` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))


fun INIT_ASSUM_TAC exp_term term_list = PAT_X_ASSUM exp_term (fn thm => ASSUME_TAC (Q.SPECL term_list thm));



val P4Exp_det =
prove (
``
(!e. det_exp e) /\
(! l: e list. det_exp_list l)
``,

Induct >|[


(*****************************)
(*       e_v case            *)
(*****************************)
RW_TAC (srw_ss()) [same_state_stmt_def, det_exp_def, Once e_red_cases]
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
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_state_stmt_def] >>
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
FULL_SIMP_TAC (srw_ss()) [is_short_circuitable_def]

)
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

IMP_RES_TAC lemma_MAP7>>
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

IMP_RES_TAC lemma_MAP5>>
RES_TAC >>	
IMP_RES_TAC lemma_args1 >>
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

IMP_RES_TAC lemma_MAP5>>
RES_TAC >>	
IMP_RES_TAC lemma_args1 >>
METIS_TAC[]

,

(*start the forth poof here*)

`SOME (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list) =
SOME (MAP (λ(e_,e'_,x_,d_). (x_,d_)) e_e'_x_d_list') ` by METIS_TAC [SOME_EL,SOME_11] >>
REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>

(**first show that the d is the same in both lists, thus the i = i'*)
REV_FULL_SIMP_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_MAP6 >>
`i = i'` by METIS_TAC [ option_case_def]>>

(*Now try to show that the EL i l is deterministic*)
REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def, det_exp_list_def] >>
PAT_ASSUM `` ∀x._``
( STRIP_ASSUME_TAC o (Q.SPECL [`(EL i (MAP (λ(e_,e'_,x_,d_). e_) (e_e'_x_d_list:(e#e#string#d)list)))` ])) >>
IMP_RES_TAC unred_arg_index_in_range  >>
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
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def, Once same_frame_exp_def ] 
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







(*


(*****************************)
(*    e_func_exec            *)
(*****************************)
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_func_exec stm)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []
>|[
(*first subgoal*)
OPEN_EXP_RED_TAC ``(e_func_exec stm)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] 
>|[
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def, Once same_state_exp_def ] 
,
OPEN_STMT_RED_TAC ``stm`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall 
,
NTAC 2 (OPEN_STMT_RED_TAC ``stm`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall)]
,

(*second subgoal*)
OPEN_EXP_RED_TAC ``e_func_exec (stmt_ret (e_v v))`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >|
[
OPEN_STMT_RED_TAC ``stmt_ret (e_v v)``>>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall 
,
FULL_SIMP_TAC (srw_ss()) [same_state_exp_def] >>
METIS_TAC [ option_case_def]]
,
(*last subgoal*)
RW_TAC (srw_ss()) [] >>
OPEN_EXP_RED_TAC ``(e_func_exec (stmt_seq (stmt_ret (e_v v)) stmt'))`` >>
REV_FULL_SIMP_TAC (srw_ss()) []
>| [
NTAC 2 (OPEN_STMT_RED_TAC ``stm`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall)
,

FULL_SIMP_TAC (srw_ss()) [same_state_exp_def] >>
METIS_TAC [ option_case_def]
]]
,

(*****************************)
(*    e_ext_call             *)
(*****************************)
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_ext_call s0 s l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >|[

(*first subgoal*)
OPEN_EXP_RED_TAC ``(e_ext_call s0 s l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []  >|[
REV_FULL_SIMP_TAC (list_ss) [] >>
IMP_RES_TAC lemma_MAP7>>
`ext(s0,MAP (λ(e_,x_,d_). e_) e_x_d_list ,state_tup stacks status_running) =
 ext(s0,MAP (λ(e_,x_,d_). e_) e_x_d_list',state_tup stacks status_running)` by METIS_TAC[] >>
REV_FULL_SIMP_TAC (srw_ss()) [same_state_exp_def] 
,
REV_FULL_SIMP_TAC (srw_ss()) [same_state_exp_def] >>
ASSUME_TAC lemma_MAP5>>
PAT_ASSUM `` ∀l l'. _ ``
( STRIP_ASSUME_TAC o (Q.SPECL [`e_x_d_list`,`e_e'_x_d_list` ])) >> 
IMP_RES_TAC lemma_args1 >>
METIS_TAC[]
]
,

(*second subgoal*)
OPEN_EXP_RED_TAC ``(e_ext_call s0 s l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []
>| [
REV_FULL_SIMP_TAC (srw_ss()) [same_state_exp_def] >>
ASSUME_TAC lemma_MAP5>>
PAT_ASSUM `` ∀l l'. _ ``
( STRIP_ASSUME_TAC o (Q.SPECL [`e_x_d_list`,`e_e'_x_d_list` ])) >> 
IMP_RES_TAC lemma_args1 >>
METIS_TAC[]
,
REV_FULL_SIMP_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_MAP6 >>
`i = i'` by METIS_TAC [option_case_def]>>
rw[] >>
(*Now try to show that the EL i l is deterministic*)
REV_FULL_SIMP_TAC (srw_ss()) [same_state_exp_def, det_exp_list_def] >>
PAT_ASSUM `` ∀x. _ ``
( STRIP_ASSUME_TAC o (Q.SPECL [`(EL i (MAP (λ(e_,e'_,x_,d_). e_) (e_e'_x_d_list:(e#e#string#d)list)))` ])) >>
IMP_RES_TAC unred_arg_index_in_range  >>
IMP_RES_TAC EL_MEM >>
RES_TAC >>
FULL_SIMP_TAC list_ss [det_exp_def]  >>
RES_TAC >>
FULL_SIMP_TAC list_ss [same_state_exp_def]>>
rw[] >> rw[] 
]]

,

(*****************************)
(*   stmt_empty              *)
(*****************************)
RW_TAC (srw_ss()) [same_state_stmt_def, det_stmt_def, Once e_red_cases]
,

(*****************************)
(*   stmt_ass                *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ass l e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

(*first + second subgoal*)
OPEN_STMT_RED_TAC ``(stmt_ass l e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []>>
REV_FULL_SIMP_TAC (srw_ss())  [assign_def, same_state_stmt_def] >>
IMP_RES_TAC lemma_v_red_forall>|[
METIS_TAC [ option_case_def]
,
FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
INIT_ASSUM_TAC (``! e. _``)
	  [ `e''`,
	    `e'''`,
	    `c`,
	    `(state_tup stacks status)`,
	    `(state_tup stacks' status')`,
	    `(state_tup stacks'³' status'³')`] >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def]
],

(*****************************)
(*   stmt_cond                *)
(*****************************)
SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_cond e stm stm'`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

(*first subgoal*)
OPEN_STMT_RED_TAC ``stmt_cond e stm stm'`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]>>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def]
,

(*****************************)
(*   stmt_declare            *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_declare s t`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]

,
(*****************************)
(*   stmt_block              *)
(*****************************)
NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_block stm`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]
,

(*****************************)
(*   stmt_ip                 *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``stmt_block_ip stm`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >- (
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def] ) >>
OPEN_STMT_RED_TAC ``e`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] 
,

(*****************************)
(*   stmt_ret                *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ret e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def] 
,

(*****************************)
(*   stmt_seq                *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_seq stm stm')`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >- (
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def, Once same_state_exp_def ] ) >>
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
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def]
,

(*****************************)
(*   stmt_trans              *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_trans e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def]
,

(*****************************)
(*   stmt_app                *)
(*****************************)
(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC `` (stmt_app s e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_exp_def]
);


*)