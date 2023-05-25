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

val _ = new_theory "p4_deter";

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



(*determinism proof of expressions*)

Theorem P4_exp_det:
 ! (ty:'a itself) .
(!  e .          det_exp e ty) /\
(! (l1: e list). det_exp_list l1 ty)  /\
(! (l2: (string#e) list) .  det_strexp_list l2 ty) /\
(! tup. det_strexp_tup tup ty)
Proof

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
QED



(**************************************************)
(**************************************************)
      (*determinism proof single frame stmt       *)
(**************************************************)
(**************************************************)

Theorem P4_stmt_det:
 !stmt ty. det_stmt stmt ty
Proof 


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
QED


(**************************************************)
(**************************************************)
         (*determinism proof statement list*)
(**************************************************)
(**************************************************)


Theorem P4_stmtl_det:
! stmtl ty. det_stmtl stmtl ty
Proof

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
QED





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
  Cases_on ‘map_to_pass q b_func_map’ >> gvs[] >>    
 Cases_on ‘scopes_to_pass q func_map b_func_map g_scope_list ’>> gvs[] >>
  Cases_on ‘tbl_to_pass q b_func_map tbl_map’ >> gvs[] >>        
  rw[] >>
  ASSUME_TAC P4_stmtl_det >>
  fs [det_stmtl_def]  >>
   rfs[same_state_def] >>
   RES_TAC >>
     fs []  >>
   ` g_scope_list''' =  g_scope_list'⁵'` by METIS_TAC [SOME_EL,SOME_11]
]

);




Theorem P4_framel_det:
 ! framel ty. det_framel framel ty
Proof 

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
  rw[]  >>          
  Cases_on ‘map_to_pass funn b_func_map’ >> gvs[] >>
  Cases_on ‘map_to_pass funn b_func_map’ >> gvs[] >>
  Cases_on  ‘tbl_to_pass funn b_func_map tbl_map’ >> gvs[] >>
  Cases_on  ‘scopes_to_pass funn func_map b_func_map g_scope_list’>> gvs[] >| [
    (*************)
    (*comp1-comp1*)
    (*************) 

    gvs[] >>   
    ASSUME_TAC P4_stmtl_det >>
    fs [det_stmtl_def]  >>
    RES_TAC >> rw[] >>
    rfs[same_state_def] >>
    ‘ g_scope_list''' =  g_scope_list'⁵'’ by METIS_TAC [SOME_EL,SOME_11]
    ,
    
    (*************)
    (*comp1-comp2*)
    (*************)       
    
    FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def] >>
    ASSUME_TAC P4_stmt_det >>
    fs [det_stmt_def, same_state_def]  >>
    RES_TAC >>
    rfs[notret_def] >>
    TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
    rw[] >>
    rfs[notret_def]>>
    IMP_RES_TAC lemma_v_red_forall >>

    gvs[] >>
    TRY (Cases_on ‘scopes_to_retrieve funn func_map b_func_map g_scope_list’) >> gvs[] >>

    RES_TAC >> gvs[] >>
    gvs[notret_def]
    ,
    
    (*************)
    (*comp2-comp1*)
    (*************)       


    FULL_SIMP_TAC (srw_ss()) [Once stmt_red_cases, same_state_def] >>
    ASSUME_TAC P4_stmt_det >>
    fs [det_stmt_def, same_state_def]  >>
    RES_TAC >>
    rfs[notret_def] >>
    TRY( OPEN_STMT_RED_TAC ``stmt_empty`` >> fs []) >>
    rw[] >>
    rfs[notret_def]>>
    IMP_RES_TAC lemma_v_red_forall >>

    gvs[] >>
    TRY (Cases_on ‘scopes_to_retrieve funn func_map b_func_map g_scope_list’) >> gvs[] >>

    RES_TAC >> gvs[] >>
    gvs[notret_def]

    ,
        
    (*************)
    (*comp2-comp2*)
    (*************)
         
    ASSUME_TAC P4_stmtl_det >>
    fs [det_stmtl_def]  >>
    RES_TAC >>
    fs [same_state_def] >> 
    gvs[] >>
          
    Cases_on ‘assign g_scope_list'³' v (lval_varname (varn_star funn))’  >> gvs[] >>
    Cases_on ‘scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'⁴'’ >> gvs[] >>
    Cases_on ‘lookup_funn_sig_body funn func_map b_func_map ext_map’ >> gvs[] >>
    Cases_on ‘scopes_to_pass funn' func_map b_func_map g_scope_list'⁵'’ >> gvs[] >>         
    Cases_on ‘copyout (MAP (λ(x_,d_). x_) x_d_list) (MAP (λ(x_,d_). d_) x_d_list) g_scope_list'⁶' scope_list' scope_list''’>>  gvs[] >>
    Cases_on ‘scopes_to_retrieve funn' func_map b_func_map g_scope_list'⁵' g_scope_list'⁸'’ >> gvs[]         
  ]
]]
QED



val _ = export_theory ();

