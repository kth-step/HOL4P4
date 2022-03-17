open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open blastLib bitstringLib;
open p4Theory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;


val STMT_SIMP = RW.ONCE_RW_TAC[stmt_red_cases] >> EVAL_TAC>> FULL_SIMP_TAC std_ss [];
val EXP_SIMP = RW.ONCE_RW_TAC[e_red_cases] >> EVAL_TAC>> FULL_SIMP_TAC std_ss [];


(* bits representations*)
val bitE    = ``v_bit ([] ,0)``;
val bitT    = ``v_bit ([T],1)``;
val bitF    = ``v_bit ([F],1)``;
val bitA    = ``v_bit (ARB)``;
val bitErr1 = ``v_err "NoErr"``;
val bitErr2 = ``v_err "PacketTooShort"``;
val bitTwo    = ``v_bit ([T;F],2)``;


(*minimalistic states representation for transition*)
val R         = ``status_running``;
val Parse_Rej = ``(status_pars_next (pars_next_pars_fin pars_finreject))``;
val Parse_Acc = ``(status_pars_next (pars_next_pars_fin pars_finaccept))``;


(*mappings from one variable to a tuple (value, lval option)*)
val map0  = ``(varn_name "x", (^bitE , NONE: lval option))``;
val map1  = ``(varn_name "x", (^bitT , NONE: lval option))``;
val map2  = ``(varn_name "x", (^bitF , NONE: lval option))``;
val map3  = ``(varn_name "y", (^bitE , NONE: lval option))``;
val map4  = ``(varn_name "y", (^bitT , NONE: lval option))``;
val map5  = ``(varn_name "y", (^bitF , NONE: lval option))``;
val map6  = ``(varn_name "z", (^bitE , NONE: lval option))``;
val map7  = ``(varn_name "z", (^bitT , NONE: lval option))``;
val map8  = ``(varn_name "z", (^bitF , NONE: lval option))``;
val map9  = ``(varn_name "x", (^bitA , NONE: lval option))``;
val map10 = ``(varn_name "x", (^bitA , NONE: lval option))``;
val map11 = ``(varn_name "parseError", (^bitErr1 , NONE: lval option))``;
val map12 = ``(varn_name "parseError", (^bitErr2 , NONE: lval option))``;
val map13 = ``(varn_name "y",         (^bitF    , SOME (lval_varname (varn_name"x"))))``;
val map14 = ``(varn_name "headers.ip.ttl", (^bitTwo, NONE:lval option)) ``;
val map15 = ``(varn_name "a", (^bitF , NONE: lval option))``;
val map16 = ``(varn_name "b", (^bitF , SOME (lval_varname (varn_name"y"))))``;
val map17 = ``(varn_name "headers.ip.ttl", (^bitF, NONE:lval option)) ``;
val map18 = ``(varn_star,  ((v_bit ([F; F],2)),NONE:lval option) )``; 
val map19 = ``(varn_star,  (v_bit (ARB),NONE:lval option) )``;
val map20 = ``(varn_star,  ((v_bit ([F; F],2)),NONE:lval option) )``;

(*scopes examples*)
val scope0 = ``(FEMPTY |+ ^map0): scope``;
val scope1 = ``(FEMPTY |+ ^map1)``;
val scope2 = ``(FEMPTY |+ ^map2)``;
val scope3 = ``(FEMPTY |+ ^map1 |+ ^map4)``;
val scope4 = ``(FEMPTY |+ ^map9)``;
val scope5 = ``(FEMPTY |+ ^map5)``;
val scope6 = ``(FEMPTY |+ ^map1 |+ ^map4|+ ^map9)``;
val scope7 = ``(FEMPTY |+ ^map5 |+ ^map9)``;
val scope8 = ``(FEMPTY |+ ^map5 |+ ^map2)``;
val scope9 = ``(FEMPTY |+ ^map7 |+ ^map11)``;
val scope10 = ``(FEMPTY |+ ^map7 |+ ^map12)``;
val scope11 = ``(FEMPTY |+ ^map4 |+ ^map2)``;
val scope13 = ``(FEMPTY |+ ^map5)``;
val scope14 = ``(FEMPTY |+ ^map13)``;
val scope15 = ``(FEMPTY |+ ^map15 |+ ^map16)``;
val scope16 = ``(FEMPTY |+ ^map14)``;
val scope17 = ``(FEMPTY |+ ^map15):scope``;
val scope18 = ``(FEMPTY |+ ^map17)``;
val scope19 = ``(FEMPTY |+ ^map4 |+ ^map2 |+ ^map18)``;
val scope20 = ``(FEMPTY |+ ^map4 |+ ^map2)``;
val scope21 = ``(FEMPTY |+ ^map1 |+ ^map4|+ ^map9)``;
val scope22 = ``(FEMPTY |+ ^map4 |+ ^map2 |+ ^map19):scope``;
val scope23 = ``(FEMPTY |+ ^map20):scope``;


(*scope list examples*)
val scopelist0 = ``[^scope0]``;
val scopelist1 = ``[^scope2]``;
val scopelist2 = ``[^scope1]``;
val scopelist3 = ``[^scope1;^scope3]``;
val scopelist4 = ``[^scope3]``;
val scopelist5 = ``[FEMPTY]: scope list``;
val scopelist6 = ``[^scope4]``;
val scopelist7 = ``[FEMPTY;^scope2]``;
val scopelist8 = ``[^scope1;^scope2]``;
val scopelist9 = ``[^scope6]``;
val scopelist10 = ``[^scope5]``;
val scopelist11 = ``[^scope5;FEMPTY]``;
val scopelist12 = ``[^scope5;^scope4]``;
val scopelist13 = ``[^scope7]``;
val scopelist14 = ``[^scope8]``;
val scopelist15 = ``[^scope9]``;
val scopelist16 = ``[^scope10]``;
val scopelist17 = ``[^scope11]``;
val scopelist18 = ``[^scope13]``;
val scopelist19 = ``[^scope2; ^scope13]``;
val scopelist20 = ``[^scope2; ^scope14]``; 
val scopelist21 = ``[^scope8; ^scope15]``; 
val scopelist22 = ``[^scope16]``;
val scopelist23 = ``[^scope8; ^scope17]``;
val scopelist24 = ``[^scope18]``;
val scopelist25 = ``[^scope11; ^scope14]``;
val scopelist26 = ``[^scope14]``;
val scopelist27 = ``[^scope19]``;
val scopelist28 = ``[^scope20]``;
val scopelist29 = ``[^scope22]``;
val scopelist30 = ``[^scope23]``;

(*empty ctrl*)
val empty_ctrl =
Define
`empty_ctrl (" ", v, match_kind_exact) = NONE:(string # e list) option`;


(*context examples*)
val ctx_empty = ``(FEMPTY, FEMPTY, FEMPTY, FEMPTY, empty_ctrl):ctx``;


(*** assignment statement reduction --concrete values -- ***)

(* test 1: Pre/post frames and states for assignment with empty global*)
val prog_ass1  = ``(stmt_ass (lval_varname (varn_name "x")) (e_v (v_bit ([T], 1))))``;
val frame1a = `` [("f", ^prog_ass1 , ^scopelist1 )] : Frame_list `` ;
val state1a = `` (state_P4 FEMPTY  ^frame1a ^R)  : state `` ;
val frame1b = `` [("f", stmt_empty , ^scopelist2 )] : Frame_list `` ;
val state1b = `` (state_P4 FEMPTY  ^frame1b ^R)  : state `` ;


val test_stmt_ass1 =
prove(`` stmt_red ^ctx_empty ^state1a ^state1b ``,
STMT_SIMP >>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]>>
FULL_SIMP_TAC list_ss []
);



(* test 2: Pre/post frames and states for assignment with non empty global*)
val frame2a = `` [("f", ^prog_ass1 , ^scopelist1 )] : Frame_list `` ;
val state2a = `` (state_P4 ^scope0  ^frame2a ^R)  : state `` ;
val frame2b = `` [("f", stmt_empty , ^scopelist2 )] : Frame_list `` ;
val state2b = `` (state_P4 ^scope0   ^frame2b ^R)  : state `` ;


val test_stmt_ass2 =
prove(`` stmt_red ^ctx_empty ^state2a ^state2b ``,
STMT_SIMP >>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]>>
FULL_SIMP_TAC list_ss []
);



(* test 3: Pre/post frames and states for assignment with expression reduction*)
val exp1   = ``(e_binop (e_v (v_bit ([T],1))) binop_add (e_v (v_bit ([F],1))))``;
val prog_ass2 = ``(stmt_ass (lval_varname (varn_name "x")) (^exp1) )``;
val prog_ass3 = ``(stmt_ass (lval_varname (varn_name "x")) (e_v (v_bit ([T],1))) )``; 
val frame3a = `` [("f", ^prog_ass2 , ^scopelist1 )] : Frame_list `` ;
val state3a = `` (state_P4 ^scope0  ^frame3a ^R)  : state `` ;
val frame3b = `` [("f", ^prog_ass3 , ^scopelist1 )] : Frame_list `` ;
val state3b = `` (state_P4 ^scope0   ^frame3b ^R)  : state `` ;


val test_stmt_ass3 =
prove(`` stmt_red ^ctx_empty ^state3a ^state3b ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);



(* test 4: Pre/post frames and states for assignment with an other value*)
val prog_ass4 = ``(stmt_ass (lval_varname (varn_name "x")) (e_var(varn_name "y")))``;
val prog_ass5 = ``(stmt_ass (lval_varname (varn_name "x")) (e_v (v_bit ([T],1))) )``;
val frame4a = `` [("f", ^prog_ass4 , ^scopelist17 )] : Frame_list `` ;
val state4a = `` (state_P4 ^scope0  ^frame4a ^R)  : state `` ;
val frame4b = `` [("f", ^prog_ass5 , ^scopelist17 )] : Frame_list `` ;
val state4b = `` (state_P4 ^scope0  ^frame4b ^R)  : state `` ;

val test_stmt_ass4 =
prove(`` stmt_red ^ctx_empty ^state4a ^state4b ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);





(*** if statement reduction  ***)
val cond1  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([F],1))))``;
val cond2  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([T],1))))``;
val prog_if1 = ``(stmt_cond  ^cond1 stmt_empty  ^prog_ass1 )``;
val prog_if2 = ``(stmt_cond  ^cond2 stmt_empty  ^prog_ass1 )``;
val prog_if3 = ``(stmt_cond (e_v (v_bool  T )) stmt_empty  ^prog_ass1 )``;
val prog_if4 = ``(stmt_cond (e_v (v_bool  F )) stmt_empty  ^prog_ass1 )``;


val frame_if1 = `` [("f", ^prog_if1 , ^scopelist1 )] : Frame_list `` ;
val state_if1 = `` (state_P4 ^scope0  ^frame_if1 ^R)  : state `` ;

val frame_if2 = `` [("f", ^prog_if3 , ^scopelist1 )] : Frame_list `` ;
val state_if2 = `` (state_P4 ^scope0  ^frame_if2 ^R)  : state `` ;

val frame_if3 = `` [("f", stmt_empty , ^scopelist1 )] : Frame_list `` ;
val state_if3 = `` (state_P4 ^scope0  ^frame_if3 ^R)  : state `` ;

val frame_if4 = `` [("f", ^prog_if2 , ^scopelist1 )] : Frame_list `` ;
val state_if4 = `` (state_P4 ^scope0  ^frame_if4 ^R)  : state `` ;

val frame_if5 = `` [("f", ^prog_if4 , ^scopelist1 )] : Frame_list `` ;
val state_if5 = `` (state_P4 ^scope0  ^frame_if5 ^R)  : state `` ;


(* test 1: tranistion for if e *)
val test_stmt_cond1 =
prove(`` stmt_red ^ctx_empty ^state_if1 ^state_if2  ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);

(* test 2: transition for if true*)
val test_stmt_cond2 =
prove(`` stmt_red ^ctx_empty ^state_if2 ^state_if3  ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);

(* test 3: transition for if e -> if false*)
val test_stmt_cond3 =
prove(`` stmt_red ^ctx_empty ^state_if4 ^state_if5  ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);



(*** declare statement reduction ***)

(*declare a variable*)
val prog_dec1  = ``(stmt_declare "x"  (t_base bt_bit) )``;

val frame_dec1 = `` [("f", ^prog_dec1 , ^scopelist5 )] : Frame_list `` ;
val state_dec1 = `` (state_P4 FEMPTY  ^frame_dec1 ^R)  : state `` ;

val frame_dec2 = `` [("f", stmt_empty , ^scopelist6 )] : Frame_list `` ;
val state_dec2 = ``(state_P4 FEMPTY  ^frame_dec2 ^R): state``;

(* test 1: transition for declare with empty global*)
val test_stmt_decl1 =
prove(`` stmt_red (^ctx_empty) ^state_dec1 ^state_dec2  ``,
STMT_SIMP >>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);


val frame_dec3 = `` [("f", ^prog_dec1 , ^scopelist5 )] : Frame_list `` ;
val state_dec3 = `` (state_P4 ^scope5  ^frame_dec1 ^R)  : state `` ;

val frame_dec4 = `` [("f", stmt_empty , ^scopelist6 )] : Frame_list `` ;
val state_dec4 = ``(state_P4 ^scope5  ^frame_dec2 ^R): state``;

(* test 2: transition for declare with non empty global*)
val test_stmt_decl2 =
prove(`` stmt_red (^ctx_empty) ^state_dec3 ^state_dec4  ``,
STMT_SIMP >>
EVAL_TAC
);



(*** block enter, exec, exit statement reduction --concrete values -- ***)
val prog_blk1 =  ``(stmt_block ^prog_if3 )``;
val prog_blk2 =  ``(stmt_block_ip ^prog_if3)``;
val prog_blk3 =  ``(stmt_block_ip stmt_empty)``;


val frame_blk1 = `` [("f", ^prog_blk1 , ^scopelist10 )] : Frame_list `` ;
val state_blk1 = ``(state_P4 FEMPTY ^frame_blk1 ^R): state``;

val frame_blk2 = `` [("f", ^prog_blk2 , ^scopelist11 )] : Frame_list `` ;
val state_blk2 = ``(state_P4 FEMPTY ( ^frame_blk2) ^R): state``;



val test_stmt_block_enter =
prove(`` stmt_red (^ctx_empty) ^state_blk1 ^state_blk2 ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_blk3 = `` [("f", ^prog_blk1 , ^scopelist10 )] : Frame_list `` ;
val state_blk3 = ``(state_P4 ^scope3 ^frame_blk3 ^R): state``;

val frame_blk4 = `` [("f", ^prog_blk2 , ^scopelist11 )] : Frame_list `` ;
val state_blk4 = ``(state_P4 ^scope3 ( ^frame_blk4) ^R): state``;

(* test 1: transition for block enter*)
val test_stmt_block_enter =
prove(`` stmt_red (^ctx_empty) ^state_blk3 ^state_blk4 ``,
STMT_SIMP >>
EVAL_TAC
);



val frame_blk5 = `` [("f", ^prog_blk3 , ^scopelist11 )] : Frame_list `` ;
val state_blk5 = ``(state_P4 ^scope3 ( ^frame_blk5) ^R): state``;


 (* test 2: transition for block exec*)
val test_stmt_block_exec =
prove(`` stmt_red (^ctx_empty) ^state_blk4 ^state_blk5  ``,
RW_TAC (srw_ss()) [Once stmt_red_cases] >>
EXISTS_TAC``^scope3`` >>
STMT_SIMP 
);


(* test 3: transition for block exit*)
val frame_blk6 = `` [("f", stmt_empty , ^scopelist10 )] : Frame_list `` ;
val state_blk6 = ``(state_P4 ^scope3 ( ^frame_blk6) ^R): state``;


val test_stmt_block_exit =
prove(`` stmt_red (^ctx_empty) ^state_blk5 ^state_blk6 ``,
STMT_SIMP >>
EVAL_TAC
);




(*** transitions stmt reduction  ***)

val prog_tra1 =  ``stmt_trans (e_v (v_str "MoveNext")) ``;
val prog_tra2 =  ``stmt_trans (e_v (v_str "accept")) ``;
val prog_tra3 =  ``stmt_trans (e_v (v_str "reject")) ``;



val frame_tra1 = `` [("f", ^prog_tra1 , ^scopelist1 )] : Frame_list `` ;
val state_tra1 = ``(state_P4 FEMPTY (^frame_tra1) ^R): state``;


val frame_tra2 = `` [("f", stmt_empty , ^scopelist1 )] : Frame_list `` ;
val state_tra2 = ``(state_P4 FEMPTY (^frame_tra2) (status_pars_next (pars_next_trans "MoveNext"))): state``;


(* test 1: transition for stmt trans to non final*)
val test_stmt_trans1 =
prove(`` stmt_red (^ctx_empty) ^state_tra1 ^state_tra2   ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_tra3 = `` [("f", ^prog_tra2 , ^scopelist1 )] : Frame_list `` ;
val state_tra3 = ``(state_P4 ^scope8 (^frame_tra3) ^R): state``;


val frame_tra4 = `` [("f", stmt_empty , ^scopelist1 )] : Frame_list `` ;
val state_tra4 = ``(state_P4 ^scope8 (^frame_tra4) ^Parse_Acc): state``;


(* test 2: transition for stmt trans to accept*)
val test_stmt_trans2 =
prove(`` stmt_red (^ctx_empty) ^state_tra3 ^state_tra4   ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_tra5 = `` [("f", ^prog_tra3 , ^scopelist1 )] : Frame_list `` ;
val state_tra5 = ``(state_P4 ^scope6 (^frame_tra5) ^R): state``;


val frame_tra6 = `` [("f", stmt_empty , ^scopelist1 )] : Frame_list `` ;
val state_tra6 = ``(state_P4 ^scope6 (^frame_tra6) ^Parse_Rej): state``;

(* test 3: transition for stmt trans to accept*)
val test_stmt_trans3 =
prove(`` stmt_red (^ctx_empty) ^state_tra5 ^state_tra6   ``,
STMT_SIMP >>
EVAL_TAC
);




(*** verify  statement reduction --concrete values -- ***)

(*Testing verify_e1 verify_e2 with both T and F evaluation *)

val prog_ver1 =  ``stmt_verify (^cond1) (e_v (v_err "PacketTooShort"))``;
val prog_ver2 =  ``stmt_verify (e_v (v_bool  T )) (e_v (v_err "PacketTooShort"))``;

val prog_ver3 =  ``stmt_verify (^cond2) (e_v (v_err "PacketTooShort"))``;
val prog_ver4 =  ``stmt_verify (e_v (v_bool  F )) (e_v (v_err "PacketTooShort"))``;

val prog_ver5 =  ``stmt_seq (stmt_ass (lval_varname (varn_name "parseError")) ((e_v (v_err "PacketTooShort")))) (stmt_trans (e_v (v_str "reject")))``;


val frame_ver1 = `` [("f", ^prog_ver1 , ^scopelist2 )] : Frame_list `` ;
val state_ver1 = ``(state_P4 ^scope8 (^frame_ver1) ^R): state``;


val frame_ver2 = `` [("f", ^prog_ver2 , ^scopelist2 )] : Frame_list `` ;
val state_ver2 = ``(state_P4 ^scope8 (^frame_ver2) ^R): state``;


(* test 1: transition for stmt verify e e -> verify T e*)

val test_stmt_verify1 =
prove(`` stmt_red (^ctx_empty) ^state_ver1 ^state_ver2  ``,
STMT_SIMP >>
EXISTS_TAC``[] : ((string # stmt # scopes_stack) list) `` >>
EXISTS_TAC``(e_v (v_bool T)) `` >>
EXP_SIMP
);


val frame_ver3 = `` [("f", stmt_empty , ^scopelist2 )] : Frame_list `` ;
val state_ver3 = ``(state_P4 ^scope8 (^frame_ver3) ^R): state``;


(* test 2: transition for stmt verify T e -> empty*)
val test_stmt_verify2 =
prove(`` stmt_red (^ctx_empty) ^state_ver2 ^state_ver3 ``,
STMT_SIMP
);




val frame_ver4 = `` [("f", ^prog_ver3 , ^scopelist2 )] : Frame_list `` ;
val state_ver4 = ``(state_P4 ^scope8 (^frame_ver4) ^R): state``;

val frame_ver5 = `` [("f", ^prog_ver4 , ^scopelist2 )] : Frame_list `` ;
val state_ver5 = ``(state_P4 ^scope8 (^frame_ver5) ^R): state``;

(* test 3: transition for stmt verify e e -> verify F e*)
val test_stmt_verify3 =
prove(`` stmt_red (^ctx_empty) ^state_ver4 ^state_ver5  ``,
STMT_SIMP >>
EXISTS_TAC``[] : ((string # stmt # scopes_stack) list) `` >>
EXISTS_TAC``(e_v (v_bool F)) `` >>
EXP_SIMP >>
EVAL_TAC
);


val frame_ver6 = `` [("f", ^prog_ver5 , ^scopelist2 )] : Frame_list `` ;
val state_ver6 = ``(state_P4 ^scope8 (^frame_ver6) ^R): state``;


(* test 4: transition for stmt verify F e -> parserError = errmsg ; trans rej*)
val test_stmt_verify4 =
prove(`` stmt_red (^ctx_empty) ^state_ver5 ^state_ver6 ``,
STMT_SIMP
);



(*Testing verify_4 the whole execustion SEQ*)

val prog_ver6 =  ``stmt_seq stmt_empty (stmt_trans (e_v (v_str "reject")))``;
val prog_ver7 =  ``(stmt_trans (e_v (v_str "reject")))``;

val frame_ver7 = `` [("f", ^prog_ver6 , ^scopelist15 )] : Frame_list `` ;
val state_ver7 = ``(state_P4 ^scope8 (^frame_ver7) ^R): state``;

val frame_ver8 = `` [("f", ^prog_ver5 , ^scopelist15 )] : Frame_list `` ;
val state_ver8 = ``(state_P4 ^scope8 (^frame_ver8) ^R): state``;

val frame_ver9 = `` [("f", ^prog_ver6 , ^scopelist16 )] : Frame_list `` ;
val state_ver9 = ``(state_P4 ^scope8 (^frame_ver9) ^R): state``;

val frame_ver10 = `` [("f", ^prog_ver7 , ^scopelist16 )] : Frame_list `` ;
val state_ver10 = ``(state_P4 ^scope8 (^frame_ver10) ^R): state``;

val frame_ver11 = `` [("f", stmt_empty , ^scopelist16 )] : Frame_list `` ;
val state_ver11 = ``(state_P4 ^scope8 (^frame_ver11) ^Parse_Rej): state``;

val test_stmt_verifyFULL =
prove(``(stmt_red (^ctx_empty) ^state_ver7 ^state_ver8)
    /\  (stmt_red (^ctx_empty) ^state_ver8 ^state_ver9)
    /\  (stmt_red (^ctx_empty) ^state_ver9 ^state_ver10)
    /\  (stmt_red (^ctx_empty) ^state_ver10 ^state_ver11)
``,
CONJ_TAC >| [
STMT_SIMP >>
DISJ1_TAC>>
 EXISTS_TAC``[] : Frame_list `` >>
 EXISTS_TAC``(stmt_ass (lval_varname "parseError")
             (e_v (v_err "PacketTooShort")))`` >>
 EXISTS_TAC``^scopelist15`` >>
 EVAL_TAC
 
,
 CONJ_TAC >| [
 STMT_SIMP >>
 DISJ1_TAC >>
 EXISTS_TAC``[] : ((string # stmt # scopes_stack) list) `` >>
 EXISTS_TAC``stmt_empty`` >>
 EXISTS_TAC``^scopelist16`` >>
 EVAL_TAC >>
 STMT_SIMP >>
 DISJ1_TAC >>
 EXISTS_TAC``[^scope8]++^scopelist16`` >>
 EVAL_TAC>>
 FULL_SIMP_TAC list_ss [FUPDATE_EQ]
,
CONJ_TAC >| [
STMT_SIMP
,
STMT_SIMP
]]]
);




(*** stmt seq  statement reduction --concrete values -- ***)
val prog_seq1  = ``(stmt_declare "x"  (t_base bt_bit) )``;
val prog_seq2  = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([F], 1))))``;
val prog_seq3 =  ``(stmt_seq ^prog_seq1 ^prog_seq2)``;
val prog_seq4 =  ``(stmt_seq stmt_empty ^prog_seq2)``;

val frame_seq1 = `` [("f", ^prog_seq3 , ^scopelist10 )] : Frame_list `` ;
val state_seq1 = ``(state_P4 ^scope8 (^frame_seq1) ^R): state``;


val frame_seq2 = `` [("f", ^prog_seq4 , ^scopelist13 )] : Frame_list `` ;
val state_seq2 = ``(state_P4 ^scope8 (^frame_seq2) ^R): state``;


(* test 1: transition for    seq dec ; x = F -> seq empty ; x= F *)
val test_stmt_seq1 =
prove(`` stmt_red (^ctx_empty) ^state_seq1 ^state_seq2 ``,
STMT_SIMP >>
DISJ1_TAC >>
RW_TAC (srw_ss()) [Once stmt_red_cases] >>
EVAL_TAC
);


(* test 2: transition for    seq empty ; x= F -> x = F*)
val frame_seq3 = `` [("f", ^prog_seq2 , ^scopelist13 )] : Frame_list `` ;
val state_seq3 = ``(state_P4 ^scope8 (^frame_seq3) ^R): state``;

val test_stmt_seq2 =
prove(`` stmt_red (^ctx_empty) ^state_seq2 ^state_seq3  ``,
STMT_SIMP 
);





(*** lookup expression  reduction --concrete values -- ***)

(* test 1: lookup e current frames stack while global empty*)
val test_e_lookup1 =
prove(`` e_red  (^ctx_empty) FEMPTY ^scopelist8
               (e_var (varn_name"x")) (e_v (v_bit ([F],1))) ([]) ``,
NTAC 2 EXP_SIMP
);

(* test 2: lookup e current frames stack while global non empty*)
val test_e_lookup2 =
prove(`` e_red  (^ctx_empty) ^scope1 ^scopelist8
               (e_var (varn_name"x")) (e_v (v_bit ([F],1))) ([]) ``,
NTAC 2 EXP_SIMP
);


(* test 3: lookup varn_star current frames stack while global non empty*)
val test_e_lookup3 =
prove(`` e_red  (^ctx_empty) FEMPTY ^scopelist30
               (e_var (varn_star)) (e_v (v_bit ([F; F],2))) ([]) ``,
NTAC 2 EXP_SIMP
);





(*** more on assignment null  ***)
val prog_null1   = ``stmt_ass lval_null (e_v (v_bit ([T],1)))``;


val frame_null1 = `` [("f", ^prog_null1 , ^scopelist7 )] : Frame_list `` ;
val state_null1 = ``(state_P4 ^scope3 (^frame_null1) ^R): state``;

val frame_null2 = `` [("f", stmt_empty , ^scopelist7 )] : Frame_list `` ;
val state_null2 = ``(state_P4 ^scope3 (^frame_null2) ^R): state``;


(* test 1: assign to null changes nothing*)
val test_stmt_ass_null =
prove(`` stmt_red (^ctx_empty) ^state_null1 ^state_null2 ``,
STMT_SIMP
);





(**************************************************************)
(*** Testing function calls reductions --concrete values -- ***)
(**************************************************************)

(****copy_in IN values aka func_call_args rule ****)

val func_sig1 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_in)] ))): func_map``;
val ctx1 = ``(FEMPTY, ^func_sig1, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_call1 = ``(e_func_call "Add1" [e_var (varn_name"x")]) ``;
val prog_call2 = ``(e_func_call "Add1" [(e_v (v_bit ([F],1)))]) ``;

(* test 1: test exp red : call Add1 (x) ~> call Add1 (1)
where the arg is IN i.e. not copied in*)

val test_COPYIN1 =
prove(`` e_red  (^ctx1) ^scope2 [FEMPTY]
           (^prog_call1)
	   (^prog_call2)  ([]) ``,
	   
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var( varn_name "x"), (e_v (v_bit ([F],1))) , "y" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 2 (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);





(* test 2: test exp red : call Add1 (x) ~> call Add1 (1)
where the arg is IN i.e. not copied in*)

val func_sig2 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_none)] ))): func_map``;
val ctx2 = ``(FEMPTY, ^func_sig2, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_COPYIN2 =
prove(`` e_red  (^ctx2) ^scope2 [FEMPTY]
           (^prog_call1)
	   (^prog_call2)  ([]) ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var ( varn_name "x"), (e_v (v_bit ([F],1))) , "y" , d_none)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 2 (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);




(* test 3: test exp red : call Add1 (y, x) ~> call Add1 (y ,1)
where y is OUT so it is copied out, thus we do not evaluate it in the first swipe
and   x is IN so it will be the first value to evaluate and not copied in *)

val func_sig3 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_out); ("b", d_in)] )))``;
val ctx3 = ``(FEMPTY, ^func_sig3, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call3 = ``(e_func_call "Add1" [e_var (varn_name "y"); e_var (varn_name "x")]) ``; (*call the function with x,y*)
val prog_call4 = ``(e_func_call "Add1" [e_var (varn_name "y"); (e_v (v_bit ([F],1)))]) ``;


val test_COPYIN3 =
prove(`` e_red (^ctx3) ^scope2 [FEMPTY]
           (^prog_call3)
	   (^prog_call4)  ([])``,
	   
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var (varn_name "y"), e_var (varn_name "y") , "a" , d_out);
              ( e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



(* test 4: test exp red : call Add1 (x, y) ~> call Add1 (1 ,y)
where x is NONE so it is not copied out, thus we do evaluate it in the first swipe
and   y is OUT  *)

val func_sig4 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_out)] )))``;
val ctx4 = ``(FEMPTY, ^func_sig4, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call5 = ``(e_func_call "Add1" [ e_var (varn_name "x"); e_var (varn_name "y")]) ``; (*call the function with a,b*)
val prog_call6 = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); e_var (varn_name "y")]) ``;


val test_COPYIN4 =
prove(``e_red (^ctx4) ^scope2 [FEMPTY]
           (^prog_call5)
	   (^prog_call6)  ([])``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var (varn_name "y"), e_var (varn_name "y") , "b" , d_out)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



(* test 5 + 6: two arguments call NONE and IN reduction sequence*)
val func_sig5 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_in)] )))``;
val ctx5 = ``(FEMPTY, ^func_sig5, FEMPTY, FEMPTY, empty_ctrl):ctx``;


val prog_call7 = ``(e_func_call "Add1" [ e_var (varn_name "x") ; e_var (varn_name "y")]) ``; 
val prog_call8 = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); e_var (varn_name "y")]) ``;
val prog_call9 = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); (e_v (v_bit ([T],1)))]) ``;


val test_COPYIN5 =
prove(`` e_red (^ctx5) ^scope11 [FEMPTY]
           (^prog_call7)
	   (^prog_call8)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[(e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "a" , d_none);
              (e_var (varn_name "y"),e_var (varn_name "y"), "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>


RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EXP_SIMP )
);



val test_COPYIN6 =
prove(`` e_red (^ctx5) ^scope11 [FEMPTY]
           (^prog_call8)
	   (^prog_call9)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1))),(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var (varn_name "y"),(e_v (v_bit ([T],1))) , "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EXP_SIMP )
);



(* test 7: one arg red with expression operation*)

val prog_call10 = ``(e_func_call "Add1" [e_binop (e_var (varn_name "x")) binop_add (e_var (varn_name "y"))]) ``; 
val prog_call11 = ``(e_func_call "Add1" [e_binop (e_v (v_bit ([F],1))) binop_add  (e_var (varn_name "y"))]) ``; 
val func_sig6 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_in)] )))``;
val ctx6 = ``(FEMPTY, ^func_sig6, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_COPYIN7 =
prove(`` e_red (^ctx6) ^scope11 [FEMPTY]
           (^prog_call10)
	   (^prog_call11)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[(e_binop  (e_var (varn_name "x")) binop_add  (e_var (varn_name "y"))),
               e_binop (e_v (v_bit ([F],1))) binop_add  (e_var (varn_name "y"))
	       , "a"
	       , d_in]`` >>
EXISTS_TAC ``(stmt_empty)`` >>


NTAC 2(
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
) >>

REPEAT (EXP_SIMP)
);




val Fn = ``called_function_name_function_name``; 

(****copy_in OUT values aka func_call_newframe rule ****)
(* test 8: copy_in IN values aka func_call_newframe rule*)

val func_sig7 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_in)] )))``;
val ctx7 = ``(FEMPTY, ^func_sig7, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_call12 = ``(e_func_call "Add1" [(e_v (v_bit ([F],1)))]) ``;


val test_NEWFRAME1 =
prove(`` e_red (^ctx7) ^scope2 [FEMPTY]
                  (^prog_call12) 
                  (e_var varn_star) [("Add1", stmt_empty , [^scope13] )]``,

EXP_SIMP >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1)))
	       , "y"
	       , d_in)]`` >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);


(******************************************************)
(****copy_in OUT values aka func_call_newframe rule ****)
(* test 9: copy_in OUT values aka func_call_newframe rule*)

val func_sig8 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_out)] )))``;
val ctx8 = ``(FEMPTY, ^func_sig8, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_call13 = ``(e_func_call "Add1" [e_var (varn_name "x")]) ``;


val test_NEWFRAME2 =
prove(`` e_red (^ctx8) ^scope2 [FEMPTY]
                  (^prog_call13) 
                  (e_var varn_star) [("Add1", stmt_empty , [^scope14] )]``,

EXP_SIMP >>
EXISTS_TAC ``[( (e_var (varn_name "x"))
	       , "y"
	       , d_out)]`` >>	       	       
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);



(****copy_in two args IN and OUT values aka func_call_newframe rule ****)
(* test 10: copy_in two arguments (NONE, OUT) values aka func_call_newframe rule*)
val ctx9 = ``(FEMPTY, ^func_sig4, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_NEWFRAME3 =
prove(`` e_red (^ctx4) ^scope0 [^scope8]
                  (^prog_call6) 
                   (e_var varn_star) [("Add1", stmt_empty , [^scope15] )] ``,
		  
EXP_SIMP >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var ( varn_name "y"), "b" , d_out)]`` >>      
EVAL_TAC
);



(**************************************************************)
(*** Testing apply and tables reductions --concrete values-- ***)
(**************************************************************)
val prog_app1 = ``stmt_app "check_ttl" (e_var (varn_name("headers.ip.ttl"))) ``;
val prog_app2 = ``stmt_app "check_ttl" (e_v (v_bit ([T; F],2))) ``;
val prog_app3 = ``stmt_ass lval_null   (e_func_call "NoAction" [])``;

val table_map1 = ``(FEMPTY |+ ("check_ttl", (e_var(varn_name ("headers.ip.ttl")) , match_kind_exact)))``;

val ctrl1 = Define
`
 ctrl1 (("check_ttl"), (v_bit ([F; F],2)), (match_kind_exact)) = SOME ("Send_to_cpu",[]:e list ) /\
 ctrl1 (("check_ttl"), (v_bit ([T; F],2)) , (match_kind_exact)) = SOME ("NoAction",[]:e list )
`;

val ctx11 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1, ctrl1):ctx``;


(* test 1: test two reductions app e -> app v -> null := call f     *)

val frame_app1 = `` [("f", ^prog_app1 , ^scopelist4 )] : Frame_list `` ;
val state_app1 = ``(state_P4 ^scope16 (^frame_app1) ^R): state``;

val frame_app2 = `` [("f", ^prog_app2 , ^scopelist4 )] : Frame_list `` ;
val state_app2 = ``(state_P4 ^scope16 (^frame_app2) ^R): state``;

val frame_app3 = `` [("f", ^prog_app3 , ^scopelist4 )] : Frame_list `` ;
val state_app3 = ``(state_P4 ^scope16 (^frame_app3) ^R): state``;


val test_APPLY1 =
prove(``
(stmt_red ^ctx11 ^state_app1 ^state_app2) /\
(stmt_red ^ctx11 ^state_app2 ^state_app3)  ``,

CONJ_TAC >|[
STMT_SIMP>>
EXP_SIMP>>
EVAL_TAC
,
NTAC 2 (RW.ONCE_RW_TAC[stmt_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [ctrl1])
]);




(* test 2: test two reductions app e -> app v -> null := call f
Where teh value is repeated in teh global and in the local stack scope *)

val prog_app4 = ``stmt_app "check_ttl" (e_v (v_bit ([F],1))) ``;
val prog_app5 = ``stmt_ass lval_null   (e_func_call "Send_to_cpu" [])``;

val frame_app4 = `` [("f", ^prog_app1 , ^scopelist24 )] : Frame_list `` ;
val state_app4 = ``(state_P4 ^scope16 (^frame_app4) ^R): state``;

val frame_app5 = `` [("f", ^prog_app4 , ^scopelist24 )] : Frame_list `` ;
val state_app5 = ``(state_P4 ^scope16 (^frame_app5) ^R): state``;

val frame_app6 = `` [("f", ^prog_app5 , ^scopelist24 )] : Frame_list `` ;
val state_app6 = ``(state_P4 ^scope16 (^frame_app6) ^R): state``;


val ctrl2 = Define
`
 ctrl2 (("check_ttl"), (v_bit ([F],1)), (match_kind_exact)) = SOME ("Send_to_cpu",[]:e list ) /\
 ctrl2 (("check_ttl"), (v_bit ([],1)), (match_kind_exact)) = SOME ("NoAction"   ,[]:e list )
`;

(*
val x = Define `
f (1,5) = 0 /\
f (1,x) = 1
`
*)

val ctx12 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1, ctrl2):ctx``;

val test_APPLY2 =
prove(``
(stmt_red ^ctx12 ^state_app4 ^state_app5) /\
(stmt_red ^ctx12 ^state_app5 ^state_app6) ``,

CONJ_TAC >|[
STMT_SIMP>>
EXP_SIMP>>
EVAL_TAC
,
NTAC 2 (RW.ONCE_RW_TAC[stmt_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [ctrl2])
]);



(**************************************************************)
(***    Testing return reductions --concrete values--       ***)
(**************************************************************)

(*test a value assigned to a function call... with a copy out
and the body of teh funtion is return *)

val func_sig10 = ``(FEMPTY |+ ("Add1", (stmt_ret (e_v (v_bit ([F;F],2))) , [("y",d_out)] )))``;
val ctx13 = ``(FEMPTY, ^func_sig10, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_ret1 = ``(stmt_ass (lval_varname (varn_name"g")) (e_func_call "Add1" [e_var (varn_name "x")]))  ``;
val prog_ret2a = ``(stmt_ret (e_v (v_bit ([F;F],2)))) ``;
val prog_ret2b = ``(stmt_ass (lval_varname (varn_name"g"))  (e_var varn_star))  ``;

val frame_ret1 = `` [("f", ^prog_ret1 , ^scopelist17 )] : Frame_list `` ;
val state_ret1 = ``(state_P4 FEMPTY (^frame_ret1) ^R): state``;

val frame_ret2a = `` [("Add1", ^prog_ret2a , ^scopelist26 )] : Frame_list `` ;
val frame_ret2b = `` [("f", ^prog_ret2b , ^scopelist17 )] : Frame_list `` ;

val state_ret2 = ``(state_P4 FEMPTY ((^frame_ret2a)++(^frame_ret2b)) ^R): state``;


(* test 1:
test reduction [f, g := call Add1 (x), oldf] -> [Add1, ret 0 , cpins]++[ f, g := * , oldf]
*)

val test_return1 =
prove(`` stmt_red ^ctx13 ^state_ret1 ^state_ret2
``,

STMT_SIMP >>
EXISTS_TAC``^frame_ret2a`` >>
EXISTS_TAC``  (e_var varn_star)``>>
EXP_SIMP >>
EXISTS_TAC ``[( e_var (varn_name "x")
	       , "y"
	       , d_out)]`` >>	       
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);




(* test 2:
test reduction [Add1, ret 0 , cpins] ++ [ f, g := * , oldf] -> [f, g = * , oldf']
with copyouts
*)

val frame_ret2a = `` [("Add1", ^prog_ret2a , ^scopelist26 )] : Frame_list `` ;
val frame_ret2b = `` [("f", ^prog_ret2b , ^scopelist28 )] : Frame_list `` ;

val state_ret2 = ``(state_P4 FEMPTY ((^frame_ret2a)++(^frame_ret2b)) ^R): state``;


val frame_ret3a = `` [("Add1", stmt_empty , ^scopelist26 )] : Frame_list `` ;
val frame_ret3b = `` [("f", ^prog_ret2b , ^scopelist27 )] : Frame_list `` ; (*same as 2a*)
val state_ret3 = ``(state_P4 FEMPTY ((^frame_ret3b)) ^R ) : state``;


val test_return2 =
prove(`` stmt_red ^ctx13 ^state_ret2 ^state_ret3 
``,
FULL_SIMP_TAC list_ss [Once stmt_red_cases ] >>
DISJ2_TAC >> DISJ1_TAC >>


EXISTS_TAC `` [("y",d_out)]`` >>
EXISTS_TAC ``FEMPTY : scope`` >>
EXISTS_TAC ``"Add1"`` >>
EXISTS_TAC ``stmt_ret (e_v (v_bit ([F; F],2)))`` >>
EXISTS_TAC ``[FEMPTY |+ (varn_name "y",v_bit ([F],1),SOME (lval_varname (varn_name "x")))]`` >>

EXISTS_TAC ``"f"`` >>
EXISTS_TAC ``stmt_ass (lval_varname (varn_name "g")) (e_var varn_star)`` >>
EXISTS_TAC ``^scopelist28`` >>
EXISTS_TAC ``[] : Frame_list`` >>
EXISTS_TAC ``FEMPTY : scope`` >>
EXISTS_TAC ``^scopelist27`` >>

EXISTS_TAC ``stmt_empty`` >>
EXISTS_TAC ``(v_bit ([F; F],2))`` >>

EXISTS_TAC ``stmt_ret (e_v (v_bit ([F; F],2)))`` >>

STMT_SIMP >>


ASSUME_TAC (finite_mapLib.fupdate_NORMALISE_CONV
``FEMPTY |+ ("y",v_bit ([T],1),NONE) |+ ("x",v_bit ([F],1),NONE) |+
   ("star",v_bit ([F; F],2),NONE) |+ ("x",v_bit ([F],1),NONE)``) >>
fs [FUPDATE_COMMUTES]
);




(* test 3:
test reduction [Add1, ret 0 , cpins] ++ [ f, g := * , oldf] -> [f, g = * , oldf']
without copyouts
*)

val frame_ret4a = `` [("Add1", ^prog_ret2a , [FEMPTY] )] : Frame_list `` ;
val frame_ret4b = `` [("f", ^prog_ret2b , ^scopelist28 )] : Frame_list `` ;
val state_ret4 = ``(state_P4 FEMPTY ((^frame_ret4a)++(^frame_ret4b)) ^R): state``;

val frame_ret5b = `` [("f", ^prog_ret2b , ^scopelist27 )] : Frame_list `` ; 
val state_ret5 = ``(state_P4 FEMPTY ((^frame_ret5b)) ^R ) : state``;


val test_return3 =
prove(`` stmt_red ^ctx7 ^state_ret4 ^state_ret5 
``,
FULL_SIMP_TAC list_ss [Once stmt_red_cases ] >>
DISJ2_TAC >> DISJ1_TAC >>


EXISTS_TAC `` [("y",d_in)]`` >>
EXISTS_TAC ``FEMPTY : scope`` >>
EXISTS_TAC ``"Add1"`` >>
EXISTS_TAC ``stmt_ret (e_v (v_bit ([F; F],2)))`` >>
EXISTS_TAC ``[FEMPTY]:scopes_stack`` >>

EXISTS_TAC ``"f"`` >>
EXISTS_TAC ``stmt_ass (lval_varname (varn_name "g")) (e_var varn_star)`` >>
EXISTS_TAC ``^scopelist28`` >>
EXISTS_TAC ``[] : Frame_list`` >>
EXISTS_TAC ``FEMPTY : scope`` >>
EXISTS_TAC ``^scopelist27`` >>


EXISTS_TAC ``stmt_empty`` >>
EXISTS_TAC ``(v_bit ([F; F],2))`` >>
EXISTS_TAC ``stmt_empty`` >>

STMT_SIMP>>
FULL_SIMP_TAC list_ss [FLOOKUP_DEF, LUPDATE_def, FUPDATE_EQ]
);


(****************************************************************)
(***Testing Headers assignment and access --concrete values-- ***)
(****************************************************************)

(*assignment*)

val header1 = `` [("dstAddr", (v_bit ([T;T],2)));
                 ("srcAddr", (v_bit ([F;F],2)));
		 ("etherType", (v_bit ([T],1)))]
		 ``;

val header2 = `` [("dstAddr", (v_bit ([T;T],2)));
                 ("srcAddr", (v_bit ([T;T],2)));
		 ("etherType", (v_bit ([T],1)))]
		 ``;


val scopelist_h1 = ``[FEMPTY |+ (varn_name "IPv4_h",((v_header (T) ^header1) , NONE:lval option))] ``;

val scopelist_h2 = ``[FEMPTY |+ (varn_name "IPv4_h",((v_header (T) ^header2) , NONE:lval option))]``;


val prog_ass_h1 = ``stmt_ass  (lval_field (lval_varname (varn_name "IPv4_h")) "srcAddr")
                                  (e_v (v_bit ([T;T],2)))``;

val prog_ass_h2 = ``stmt_ass  (lval_varname (varn_name "IPv4_h"))
                                  (e_v (v_header (T) ^header2)) ``;


val frame_ass_h1 = `` [("f", ^prog_ass_h1 , ^scopelist_h1 )] : Frame_list `` ;
val state_ass_h1 = ``(state_P4 FEMPTY (^frame_ass_h1) ^R): state``;

val frame_ass_h2 = `` [("f", stmt_empty , ^scopelist_h2 )] : Frame_list `` ;
val state_ass_h2 = ``(state_P4 FEMPTY (^frame_ass_h2) ^R): state``;


(* test 1: test assigning a value to a header feild *)

val test_ass_h1 =
prove(`` stmt_red ^ctx_empty ^state_ass_h1 ^state_ass_h2
``,
STMT_SIMP >>
DISJ1_TAC >>
FULL_SIMP_TAC std_ss [] >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [FUPDATE_EQ]
);




(* test 2: test assigning a whole header to a header feild *)

val header3 = `` [("dstAddr", (v_bit ([F;F],2)));
                 ("srcAddr", (v_bit ([F;F],2)));
		 ("etherType", (v_bit ([T],1)))]
		 ``;


val scopelist_h3 = ``[FEMPTY |+ (varn_name "IPv4_h",((v_header (T) ^header3) , NONE:lval option))]``;


val prog_ass_h3 = ``stmt_ass  (lval_varname (varn_name "IPv4_h"))
                                (e_v (v_header (T) ^header3))``;



val frame_ass_h3 = `` [("f", ^prog_ass_h3 , ^scopelist_h2 )] : Frame_list `` ;
val state_ass_h3 = ``(state_P4 FEMPTY (^frame_ass_h3) ^R): state``;


val frame_ass_h4 = `` [("f", stmt_empty , ^scopelist_h3 )] : Frame_list `` ;
val state_ass_h4 = ``(state_P4 FEMPTY (^frame_ass_h4) ^R): state``;


val test_ass_h3 =
prove(`` stmt_red (^ctx_empty) ^state_ass_h3 ^state_ass_h4
``,
STMT_SIMP >>
DISJ1_TAC >>
FULL_SIMP_TAC std_ss [] >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [FUPDATE_EQ]
);





(*access fields*)

val prog_acc_h1 = ``e_acc (e_v (v_header (T) (^header1))) (e_v( v_str "srcAddr"))  ``;
val prog_acc_h2 = ``e_v  (v_bit ([F; F],2)) ``;


val test_acc_h1 =
prove(`` e_red (^ctx_empty) FEMPTY ^scopelist_h1
               (^prog_acc_h1) (^prog_acc_h2) ([])
``,
REPEAT EXP_SIMP
);








(**************************************************************)
(***        Testing structs    --concrete values--          ***)
(**************************************************************)


val struct1 = ``[("Ethernet_h", (v_bit ([T;T],2)));
                 ("IPv4_h", (v_header (T) ^header1))]``;


val struct2 = ``[("Ethernet_h", (v_bit ([F;F],2)));
                 ("IPv4_h", (v_header (T) ^header1))]``;


val scopelist_s1 =``[FEMPTY |+ (varn_name "Parsed_packet", ((v_struct ^struct1), NONE:lval option))]``;
val scopelist_s2 =``[FEMPTY |+ (varn_name "Parsed_packet", ((v_struct ^struct2), NONE:lval option))]``;

val prog_ass_s1 = ``stmt_ass  (lval_field (lval_varname (varn_name "Parsed_packet")) "Ethernet_h")
                                  (e_v (v_bit ([F;F],2)))``;


val frame_ass_s1 = `` [("f", ^prog_ass_s1 , ^scopelist_s1 )] : Frame_list `` ;
val state_ass_s1 = ``(state_P4 FEMPTY (^frame_ass_s1) ^R): state``;

val frame_ass_s2 = `` [("f", stmt_empty , ^scopelist_s2 )] : Frame_list `` ;
val state_ass_s2 = ``(state_P4 FEMPTY (^frame_ass_s2) ^R): state``;


val test_ass_s1 =
prove(`` stmt_red ^ctx_empty ^state_ass_s1 ^state_ass_s2       		  
``,
STMT_SIMP >>
DISJ1_TAC >>
FULL_SIMP_TAC std_ss [] >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [FUPDATE_EQ]
);


val prog_acc_h1 = ``e_acc (e_v (v_header (T) (^header1))) (e_v( v_str "srcAddr"))  ``;
val prog_acc_h2 = ``e_v  (v_bit ([F; F],2)) ``;


val prog_acc_s1 = ``e_acc (e_v (v_struct (^struct1))) (e_v( v_str "IPv4_h"))  ``;
val prog_acc_s2 = ``e_v  (v_header (T) (^header1) ) ``;


val test_acc_h1 =
prove(`` e_red  (^ctx_empty) FEMPTY ^scopelist_s1
                  ^prog_acc_s1 ^prog_acc_s2 ([])
``,
NTAC 2 EXP_SIMP
);


(****************************************************************)
(***          Testing A block calling a function              ***)
(****************************************************************)


(*

JR (out y)    //Just Return function
{
Return ((e_v (v_bit ([F;F],2));
}



f()
{
  {
    <--- start from here
    g := call JR (x)
  }
}

*)

(*

val func_sig11 = ``(FEMPTY |+ ("JR", (stmt_ret (e_v (v_bit ([F;F],2))) , [("y",d_out)] )))``;
val ctx13 = ``(FEMPTY, ^func_sig11, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_test1 = ``(stmt_ass (lval_varname "g") (e_func_call "JR" [e_var "x"]))  ``;

val prog_test2a = ``(stmt_ret (e_v (v_bit ([F;F],2)))) ``;
val prog_test2b = ``(stmt_ass (lval_varname "g") (e_var "star") ) ``;

val frame_test1 = `` [("f", ^prog_ret1 , ^scopelist17 )] : Frame_list `` ;
val state_test1 = ``(state_P4 FEMPTY (^frame_ret1) ^R): state``;



val frame_ret2a = `` [("JR", ^prog_ret2a , ^scopelist26 )] : Frame_list `` ;
val frame_ret2b = `` [("f", ^prog_ret2b , ^scopelist17 )] : Frame_list `` ;

val state_ret2 = ``(state_P4 FEMPTY ((^frame_ret2a)++(^frame_ret2b)) ^R): state``;


(* test 1:
test reduction [f, g := call Add1 (x), oldf] -> [Add1, ret 0 , cpins]++[ f, g := * , oldf]
*)

val test_return1 =
prove(`` stmt_red ^ctx13 ^state_ret1 ^state_ret2
``,

STMT_SIMP >>
EXISTS_TAC``^frame_ret2a`` >>
EXISTS_TAC`` (e_var "star")``>>
EXP_SIMP >>
EXISTS_TAC ``[( (e_var "x")
	       , "y"
	       , d_out)]`` >>
EXISTS_TAC ``^scopelist17`` >>	       
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);

*)


(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)

(******** SAME SATE and EXP DEF ************)
(*********Mapping equv. lemmas ************)


open ottTheory;
open pairTheory;
open rich_listTheory;

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

Cases_on `(is_d_none_in h ∧ ¬is_const h')` >| [
FULL_SIMP_TAC (list_ss) [is_arg_red_def]
,
STRIP_TAC >>
FULL_SIMP_TAC (list_ss) [find_unred_arg_def] >>
FULL_SIMP_TAC (list_ss) [INDEX_FIND_def, ZIP_def]>>
FULL_SIMP_TAC (list_ss) [is_arg_red_def]>>
STRIP_TAC >>
DISJ2_TAC>>
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

(*******************************************)


fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))



val same_frame_exp_def = Define `
 same_frame_exp (frame:Frame_list) frame' (e:e) e'  =
((frame = frame') /\ (e = e'))
`;


val lemma_v_red_forall =
prove(`` ! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl   ``,
RW_TAC (srw_ss()) [Once e_red_cases]
);



val det_exp_def = Define `
 det_exp e = ! c scope scopest e' e'' frame frame'.
(e_red c scope scopest e e' frame )
/\
(e_red c scope scopest e e'' frame' ) 
==>
(same_frame_exp frame frame' e' e'')
`;


val det_exp_list_def = Define `
   det_exp_list (l : e list)  = !(x : e). MEM x l ==> det_exp(x)
`;

(*Replace the one that in p4_exec_semTheory once fixed*)
Theorem unred_arg_index_in_range:
 !d_l e_l i. unred_arg_index d_l e_l = SOME i ==> i < LENGTH e_l
Proof
cheat
QED



val P4EXP_det =
prove (
``
(!e. det_exp e) /\
(! l: e list. det_exp_list l)
``,
Induct >| [
RW_TAC (srw_ss()) [same_frame_exp_def, det_exp_def, Once e_red_cases]
,
RW_TAC (srw_ss()) [det_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def, Once e_red_cases, same_frame_exp_def]
,
RW_TAC (srw_ss()) [det_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def, Once e_red_cases, same_frame_exp_def]
,
RW_TAC (srw_ss()) [det_exp_def] >>
FULL_SIMP_TAC (srw_ss()) [Once e_red_cases, same_frame_exp_def]
,

NTAC 2 (
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``e_acc e e'`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []) >>
TRY (OPEN_EXP_RED_TAC ``(e_acc (e_v (_)) (e_v (_)))`` ) >>
RW_TAC (srw_ss()) [] >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def] >>
RES_TAC 
,

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
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def]
) >-  (

              (*e_binop (e_v v) b e'*)
OPEN_EXP_RED_TAC ``(e_binop (e_v v) b e')`` >>
RW_TAC (srw_ss()) []>>
IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def] ) >> (
(*e_mul case and after, use those as much as needed.*)
OPEN_EXP_RED_TAC ``(e_binop a b c)`` >>
RW_TAC (srw_ss()) [] >>
IMP_RES_TAC lemma_v_red_forall >>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall, same_frame_exp_def, option_case_def])


,

SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_concat e e')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []

,

SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_slice e e' e'')`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []

,


(*****************************)
(*    e_func_call            *)
(*****************************)
SIMP_TAC (srw_ss()) [det_exp_def] >>
REPEAT STRIP_TAC >>
OPEN_EXP_RED_TAC ``(e_func_call s l)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>
RW_TAC (srw_ss()) []  >| [

(*first subgoal*)
OPEN_EXP_RED_TAC ``(e_func_call s l)`` >>
RW_TAC (srw_ss()) [] >| [

REV_FULL_SIMP_TAC (list_ss) [rich_listTheory.MAP_FST_funs, same_frame_exp_def] >>
IMP_RES_TAC lemma_MAP4>>
METIS_TAC []
,
REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
IMP_RES_TAC lemma_MAP5>>
RES_TAC >>	
IMP_RES_TAC lemma_args1 >>
METIS_TAC[]]
,
(*second subgoal*)
OPEN_EXP_RED_TAC ``(e_func_call s l)`` >>
RW_TAC (srw_ss()) [] >|[

REV_FULL_SIMP_TAC (srw_ss()) [same_frame_exp_def] >>
ASSUME_TAC lemma_MAP5>>
PAT_ASSUM `` ∀l l'. _ ``
( STRIP_ASSUME_TAC o (Q.SPECL [`e_x_d_list`,`e_e'_x_d_list` ])) >> 
IMP_RES_TAC lemma_args1 >>
METIS_TAC[]
,
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
]
]

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
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def ] 

,

FULL_SIMP_TAC list_ss [det_exp_list_def]
,

FULL_SIMP_TAC list_ss [det_exp_list_def] >>
REPEAT STRIP_TAC >>
rw []

]
);




(******** SAME SATE and STMT DEF ************)
val same_state_stmt_def = Define `
 same_state_stmt (st:state) st'  =
((st = st'))
`;


val det_stmt_def = Define `
 det_stmt stm = ! (c:ctx) (ss:scopes_stack) (s':state) (s'':state) (Gscope:Gscope) (f:string) status.
(stmt_red c (state_P4 Gscope  ([(f,stm,ss)])  status) (s'))
/\
(stmt_red c (state_P4 Gscope  ([(f,stm,ss)])  status) (s''))
==>
( same_state_stmt s' s'')
`;




fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red c (state_P4 Gs [(f,^stm_term ,ss)] st) state` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))






val P4Sem_det =
prove (
``
(!stm. det_stmt stm) 
``

Induct >|[
RW_TAC (srw_ss()) [det_stmt_def] >>
OPEN_STMT_RED_TAC ``stmt_empty`` >>
fs []
,


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
ASSUME_TAC P4EXP_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]
]

,

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
FULL_SIMP_TAC (srw_ss()) [det_stmt_def,lemma_v_red_forall] >>

ASSUME_TAC P4EXP_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]

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
OPEN_STMT_RED_TAC ``stmt_empty`` >>
REV_FULL_SIMP_TAC (srw_ss()) []
,
(*****************************)
(*   stmt_ret                *)
(*****************************)
(NTAC 2 ( SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ret e)`` >>
REV_FULL_SIMP_TAC (srw_ss()) [] ) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>

FULL_SIMP_TAC (srw_ss()) [det_exp_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def] >>
IMP_RES_TAC lemma_v_red_forall>>

ASSUME_TAC P4EXP_det >>
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
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
FULL_SIMP_TAC (srw_ss()) [det_stmt_def] >>
RES_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def, Once same_frame_exp_def ] >>
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
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def]>>
ASSUME_TAC P4EXP_det >>
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
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def]) >>
IMP_RES_TAC lemma_v_red_forall>>
FULL_SIMP_TAC (srw_ss()) [det_exp_def,lemma_v_red_forall] >>
RES_TAC>>
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def] >>
ASSUME_TAC P4EXP_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]

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
FULL_SIMP_TAC (srw_ss()) [Once same_frame_exp_def]>>
ASSUME_TAC P4EXP_det >>
fs [det_exp_def]  >>
RES_TAC >>
fs [same_frame_exp_def]

,

(NTAC 2 (SIMP_TAC (srw_ss()) [det_stmt_def] >>
REPEAT STRIP_TAC >>
OPEN_STMT_RED_TAC ``(stmt_ext_sem)`` >>
REV_FULL_SIMP_TAC (srw_ss()) []) >> 
FULL_SIMP_TAC (srw_ss()) [Once same_state_stmt_def] ) >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

???
]);

