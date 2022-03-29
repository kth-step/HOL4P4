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



(*definition to make a bit list value  from a number*)
val mk_v_def = Define `
mk_v v = (v_bit ( n2v v , LENGTH(n2v v) )) 
`;


(* make expressions *)
val mk_b_def = Define `
mk_b (b:bool) = e_v (v_bool  b )
`;

(*definition to make a bit list expression from a number *)
val mk_e_def = Define `
mk_e v = (e_v (mk_v v) )
`;


(*definition to make a tuple of a mapping*)
val mk_map_def = Define `
(mk_map x v  (n:lval option)= (varn_name x, (mk_v v , n)))
`;

val mk_decl_map_def = Define `
mk_decl_map x (n:lval option) = (varn_name x, (v_bit (ARB) , n))
`;

val mk_star_def = Define `
(mk_star v  (n:lval option)= (varn_star, (mk_v v , n)))
`;


(*definition to make arb vals*)
val mk_init_map_def = Define `
(mk_init_map x v (n:lval option) = (varn_name x, (init_out_v (v_bit (v)) , n ))) 
`;

val mk_init_map_s_def = Define `
(mk_init_map_s v (n:lval option) = (varn_star, (init_out_v (v_bit (v)) , n ))) 
`;


(*minimalistic states representation for transition*)
val R         = ``status_running``;
val Parse_Rej = ``(status_pars_next (pars_next_pars_fin pars_finreject))``;
val Parse_Acc = ``(status_pars_next (pars_next_pars_fin pars_finaccept))``;


(*mappings from one variable to a tuple (value, lval option)*)
val map11 = ``(varn_name "parseError", (v_err "NoErr" , NONE: lval option))``;
val map12 = ``(varn_name "parseError", (v_err "PacketTooShort" , NONE: lval option))``;
val map_initx_arb = ``mk_init_map "x" ([], 1) NONE``;
val map_y_somex = ``mk_init_map "y" ([], 1) (SOME (lval_varname (varn_name"x")))``;
val map_b_somey = ``mk_init_map "b" ([], 1) (SOME (lval_varname (varn_name"y")))``;
val map_s_ff = ``(varn_star,  ((v_bit ([F; F],2)),NONE:lval option) )``; 


(*scope list examples*)
val scopelist1 = ``[FEMPTY |+ mk_map "x" 0 NONE]``;
val scopelist2 = ``[FEMPTY |+ mk_map "x" 1 NONE]``;
val scopelist3 = ``[FEMPTY; (FEMPTY |+ (mk_map "x" 1 NONE))]``;
val scopelist4 = ``[(FEMPTY |+ (mk_map "x" 1 NONE) |+ (mk_map "y" 1 NONE))]``;
val scopelist5 = ``[(FEMPTY |+ (mk_map "x" 0 NONE)) ; (FEMPTY |+ (mk_map "y" 0 NONE) |+ (mk_map "x" 0 NONE))]: scope list``;
val scopelist6 = ``[FEMPTY |+ mk_decl_map "x" NONE]``;
val scopelist7 = ``[FEMPTY; (FEMPTY |+ (mk_map "x" 0 NONE))]``;
val scopelist8 = ``[(FEMPTY |+ (mk_map "x" 1 NONE));(FEMPTY |+ (mk_map "x" 0 NONE))]``;
val scopelist9 = ``[FEMPTY; (FEMPTY |+ (mk_map "x" 1 NONE) |+ (mk_map "y" 1 NONE) |+ (mk_decl_map "x" NONE))]``;
val scopelist10 = ``[(FEMPTY |+ (mk_map "y" 0 NONE))]``;
val scopelist11 = ``[(FEMPTY |+ (mk_map "y" 0 NONE));FEMPTY]``;
val scopelist12 = ``[(FEMPTY |+ (mk_map "y" 0 NONE) |+ (mk_map "x" 0 NONE))]``;
val scopelist13 = ``[(FEMPTY |+ (mk_map "y" 0 NONE) |+ (mk_decl_map "x" NONE))]``;
val scopelist14 = ``[FEMPTY; (FEMPTY |+ (mk_map "y" 0 NONE) |+ (mk_map "x" 0 NONE))]``;
val scopelist15 = ``[(FEMPTY |+ (mk_map "z" 1 NONE) |+ ^map11)]``;
val scopelist16 = ``[(FEMPTY |+ (mk_map "z" 1 NONE) |+ ^map12)]``;
val scopelist17 = ``[FEMPTY; (FEMPTY |+ (mk_map "y" 1 NONE) |+ (mk_map "x" 0 NONE))]``;
val scopelist18 = ``[FEMPTY; (FEMPTY |+ (mk_map "x" 1 NONE) |+ (mk_map "y" 1 NONE))]``;
val scopelist19 = ``[(FEMPTY |+ (mk_map "x" 0 NONE)); (FEMPTY |+ (mk_map "y" 0 NONE))]``;
val scopelist20 = ``[FEMPTY; (FEMPTY |+ (mk_map "y" 0 NONE))]``; 
val scopelist21 = ``[(FEMPTY |+ (mk_map "a" 0 NONE) |+ ^map_b_somey)]``; 
val scopelist22 = ``[FEMPTY; (FEMPTY |+ (mk_map "headers.ip.ttl" 2 NONE))]``;
val scopelist23 = ``[(FEMPTY |+ (mk_map "headers.ip.ttl" 0 NONE))]``;
val scopelist25 = ``[(FEMPTY |+ ^map_y_somex)]``;
val scopelist26 = ``[(FEMPTY |+ (mk_map "y" 1 NONE) |+ (mk_map "x" 0 NONE) |+ ^map_s_ff)]``;
val scopelist27 = ``[(FEMPTY |+ ^map_s_ff)]``;
val scopelist28 = ``[(FEMPTY |+ (mk_map "y" 1 NONE) |+ ^map_initx_arb |+ ^map_s_ff)]``;

(*empty ctrl*)
val empty_ctrl =
Define
`empty_ctrl (" ", v, match_kind_exact) = NONE:(string # e list) option`;


(*context examples*)
val ctx_empty = ``(FEMPTY, FEMPTY, FEMPTY, FEMPTY):ctx``;
val Gscope_list = ``[FEMPTY;FEMPTY]:scope list``;

(*** assignment statement reduction --concrete values -- ***)

(* test 1: Pre/post frames and states for assignment with empty global*)
val prog_ass1  = ``(stmt_ass (lval_varname (varn_name "x")) (e_v (v_bit ([T], 1))))``;
val frame1a = `` [(funn_name "f", ^prog_ass1 , ^scopelist1 )] : frame_list `` ;
val state1a = `` (^Gscope_list, ^frame1a, empty_ctrl, ^R):state  `` ;
val frame1b = `` [(funn_name "f", stmt_empty , ^scopelist2 )] : frame_list `` ;
val state1b = `` (^Gscope_list, ^frame1b ,  empty_ctrl,  ^R)  : state `` ;


val test_stmt_ass1 =
prove(`` stmt_red ^ctx_empty ^state1a ^state1b ``,
STMT_SIMP >>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]>>
FULL_SIMP_TAC list_ss []
);



(* test 2: Pre/post frames and states for assignment with non empty global*)
val frame2a = `` [(funn_name "f", ^prog_ass1 , ^scopelist1 )] : frame_list `` ;
val state2a = `` (^scopelist7,  ^frame2a, empty_ctrl, ^R)  : state `` ;
val frame2b = `` [(funn_name "f", stmt_empty , ^scopelist2 )] : frame_list `` ;
val state2b = `` (^scopelist7,  ^frame2b, empty_ctrl, ^R)  : state `` ;


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
val frame3a = `` [(funn_name "f", ^prog_ass2 , ^scopelist1 )] : frame_list `` ;
val state3a = `` (^scopelist7, ^frame3a, empty_ctrl, ^R)  : state `` ;
val frame3b = `` [(funn_name "f", ^prog_ass3 , ^scopelist1 )] : frame_list `` ;
val state3b = `` (^scopelist7, ^frame3b, empty_ctrl, ^R)  : state `` ;


val test_stmt_ass3 =
 prove(`` stmt_red ^ctx_empty ^state3a ^state3b ``,
STMT_SIMP >>
REPEAT (EXP_SIMP)
);



(* test 4: Pre/post frames and states for assignment with an other value*)
val prog_ass4 = ``(stmt_ass (lval_varname (varn_name "x")) (e_var(varn_name "y")))``;
val prog_ass5 = ``(stmt_ass (lval_varname (varn_name "x")) (e_v (v_bit ([T],1))) )``;
val frame4a = `` [(funn_name "f", ^prog_ass4 , ^scopelist17 )] : frame_list `` ;
val state4a = `` (^scopelist7,  ^frame4a, empty_ctrl, ^R)  : state `` ;
val frame4b = `` [(funn_name "f", ^prog_ass5 , ^scopelist17 )] : frame_list `` ;
val state4b = `` (^scopelist7,  ^frame4b, empty_ctrl, ^R)  : state `` ;

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


val frame_if1 = `` [(funn_name "f", ^prog_if1 , ^scopelist1 )] : frame_list `` ;
val state_if1 = `` (^scopelist7,  ^frame_if1, empty_ctrl, ^R)  : state `` ;

val frame_if2 = `` [(funn_name "f", ^prog_if3 , ^scopelist1 )] : frame_list `` ;
val state_if2 = `` (^scopelist7,  ^frame_if2 , empty_ctrl, ^R)  : state `` ;

val frame_if3 = `` [(funn_name "f", stmt_empty , ^scopelist1 )] : frame_list `` ;
val state_if3 = `` (^scopelist7,  ^frame_if3 , empty_ctrl, ^R)  : state `` ;

val frame_if4 = `` [(funn_name "f", ^prog_if2 , ^scopelist1 )] : frame_list `` ;
val state_if4 = `` (^scopelist7,  ^frame_if4 , empty_ctrl, ^R)  : state `` ;

val frame_if5 = `` [(funn_name "f", ^prog_if4 , ^scopelist1 )] : frame_list `` ;
val state_if5 = `` (^scopelist7,  ^frame_if5 , empty_ctrl, ^R)  : state `` ;


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
val prog_dec1  = ``(stmt_declare  (t_base bt_bit) "x"  (NONE:e option) )``;

val frame_dec1 = `` [(funn_name "f", ^prog_dec1 , [FEMPTY] )] : frame_list `` ;
val state_dec1 = `` (^Gscope_list,  ^frame_dec1 , empty_ctrl, ^R)  : state `` ;

val frame_dec2 = `` [(funn_name "f", stmt_empty , ^scopelist6 )] : frame_list `` ;
val state_dec2 = ``(^Gscope_list ,  ^frame_dec2 , empty_ctrl, ^R): state``;

(* test 1: transition for declare with empty global*)
val test_stmt_decl1 =
prove(`` stmt_red (^ctx_empty) ^state_dec1 ^state_dec2  ``,
STMT_SIMP >>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);


val frame_dec3 = `` [(funn_name "f", ^prog_dec1 , [FEMPTY] )] : frame_list `` ;
val state_dec3 = `` (^scopelist20,  ^frame_dec1 , empty_ctrl, ^R)  : state `` ;

val frame_dec4 = `` [(funn_name "f", stmt_empty , ^scopelist6 )] : frame_list `` ;
val state_dec4 = ``(^scopelist20,  ^frame_dec2 , empty_ctrl, ^R): state``;

(* test 2: transition for declare with non empty global*)
val test_stmt_decl2 =
prove(`` stmt_red (^ctx_empty) ^state_dec3 ^state_dec4  ``,
STMT_SIMP >>
EVAL_TAC
);


(*** initilize statement reduction ***)
val prog_init1  = ``(stmt_declare  (t_base bt_bit) "x"  (SOME  (e_v (v_bit ([F],1)))) )``;

val frame_init1 = `` [(funn_name "f", ^prog_init1 , ^scopelist19 )] : frame_list `` ;
val state_init1 = `` (^Gscope_list,  ^frame_init1 , empty_ctrl, ^R)  : state `` ;

val frame_init2 = `` [(funn_name "f", stmt_empty , ^scopelist5 )] : frame_list `` ;
val state_init2 = ``(^Gscope_list ,  ^frame_init2 , empty_ctrl, ^R): state``;


(* test1: test init variable x in a scope stack that has already x in the first scope*)
val test_stmt_init =
prove(`` stmt_red (^ctx_empty) ^state_init1 ^state_init2  ``,
STMT_SIMP >>
EXP_SIMP >>
EXISTS_TAC ``"x"``>>
EVAL_TAC
);



val prog_init2  = ``(stmt_declare  (t_base bt_bit) "x"  (SOME  (e_var (varn_name "y"))))``;

val frame_init3 = `` [(funn_name "f", ^prog_init2 , ^scopelist19 )] : frame_list `` ;
val state_init3 = `` (^Gscope_list,  ^frame_init3 , empty_ctrl, ^R)  : state `` ;

val frame_init4 = `` [(funn_name "f", ^prog_init1 , ^scopelist19 )] : frame_list `` ;
val state_init4 = ``(^Gscope_list ,  ^frame_init4 , empty_ctrl, ^R): state``;


(* test2: test init with e red*)
val test_stmt_init2 =
prove(`` stmt_red (^ctx_empty) ^state_init3 ^state_init4  ``,
STMT_SIMP >>
EXP_SIMP >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] 
);



(*** block enter, exec, exit statement reduction --concrete values -- ***)
val prog_blk1 =  ``(stmt_block ^prog_if3 )``;
val prog_blk2 =  ``(stmt_block_ip ^prog_if3)``;
val prog_blk3 =  ``(stmt_block_ip stmt_empty)``;


val frame_blk1 = `` [(funn_name "f", ^prog_blk1 , ^scopelist10 )] : frame_list `` ;
val state_blk1 = ``(^Gscope_list , ^frame_blk1 , empty_ctrl, ^R): state``;

val frame_blk2 = `` [(funn_name "f", ^prog_blk2 , ^scopelist11 )] : frame_list `` ;
val state_blk2 = ``(^Gscope_list , ( ^frame_blk2) , empty_ctrl, ^R): state``;



val test_stmt_block_enter =
prove(`` stmt_red (^ctx_empty) ^state_blk1 ^state_blk2 ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_blk3 = `` [(funn_name "f", ^prog_blk1 , ^scopelist10 )] : frame_list `` ;
val state_blk3 = ``(^scopelist18, ^frame_blk3 , empty_ctrl, ^R): state``;

val frame_blk4 = `` [(funn_name "f", ^prog_blk2 , ^scopelist11 )] : frame_list `` ;
val state_blk4 = ``(^scopelist18, ( ^frame_blk4) , empty_ctrl, ^R): state``;

(* test 1: transition for block enter*)
val test_stmt_block_enter =
prove(`` stmt_red (^ctx_empty) ^state_blk3 ^state_blk4 ``,
STMT_SIMP >>
EVAL_TAC
);



val frame_blk5 = `` [(funn_name "f", ^prog_blk3 , ^scopelist11 )] : frame_list `` ;
val state_blk5 = ``(^scopelist18, ( ^frame_blk5) , empty_ctrl, ^R): state``;


 (* test 2: transition for block exec*)
val test_stmt_block_exec =
prove(`` stmt_red (^ctx_empty) ^state_blk4 ^state_blk5  ``,
RW_TAC (srw_ss()) [Once stmt_red_cases] >>
EXISTS_TAC``^scopelist18`` >>
STMT_SIMP 
);


(* test 3: transition for block exit*)
val frame_blk6 = `` [(funn_name "f", stmt_empty , ^scopelist10 )] : frame_list `` ;
val state_blk6 = ``(^scopelist18, ( ^frame_blk6) , empty_ctrl, ^R): state``;


val test_stmt_block_exit =
prove(`` stmt_red (^ctx_empty) ^state_blk5 ^state_blk6 ``,
STMT_SIMP >>
EVAL_TAC
);




(*** transitions stmt reduction  ***)

val prog_tra1 =  ``stmt_trans (e_v (v_str "MoveNext")) ``;
val prog_tra2 =  ``stmt_trans (e_v (v_str "accept")) ``;
val prog_tra3 =  ``stmt_trans (e_v (v_str "reject")) ``;



val frame_tra1 = `` [(funn_name "f", ^prog_tra1 , ^scopelist1 )] : frame_list `` ;
val state_tra1 = ``(^Gscope_list , (^frame_tra1) , empty_ctrl, ^R): state``;


val frame_tra2 = `` [(funn_name "f", stmt_empty , ^scopelist1 )] : frame_list `` ;
val state_tra2 = ``(^Gscope_list , (^frame_tra2), empty_ctrl, (status_pars_next (pars_next_trans "MoveNext"))): state``;


(* test 1: transition for stmt trans to non final*)
val test_stmt_trans1 =
prove(`` stmt_red (^ctx_empty) ^state_tra1 ^state_tra2   ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_tra3 = `` [(funn_name "f", ^prog_tra2 , ^scopelist1 )] : frame_list `` ;
val state_tra3 = ``(^scopelist14, (^frame_tra3) , empty_ctrl, ^R): state``;


val frame_tra4 = `` [(funn_name "f", stmt_empty , ^scopelist1 )] : frame_list `` ;
val state_tra4 = ``(^scopelist14, (^frame_tra4) , empty_ctrl, ^Parse_Acc): state``;


(* test 2: transition for stmt trans to accept*)
val test_stmt_trans2 =
prove(`` stmt_red (^ctx_empty) ^state_tra3 ^state_tra4   ``,
STMT_SIMP >>
EVAL_TAC
);


val frame_tra5 = `` [(funn_name "f", ^prog_tra3 , ^scopelist1 )] : frame_list `` ;
val state_tra5 = ``(^scopelist9, (^frame_tra5) , empty_ctrl, ^R): state``;


val frame_tra6 = `` [(funn_name "f", stmt_empty , ^scopelist1 )] : frame_list `` ;
val state_tra6 = ``(^scopelist9, (^frame_tra6) , empty_ctrl, ^Parse_Rej): state``;

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


val frame_ver1 = `` [(funn_name "f", ^prog_ver1 , ^scopelist2 )] : frame_list `` ;
val state_ver1 = ``(^scopelist14, (^frame_ver1) , empty_ctrl, ^R): state``;


val frame_ver2 = `` [(funn_name "f", ^prog_ver2 , ^scopelist2 )] : frame_list `` ;
val state_ver2 = ``(^scopelist14, (^frame_ver2) , empty_ctrl, ^R): state``;


(* test 1: transition for stmt verify e e -> verify T e*)

val test_stmt_verify1 =
prove(`` stmt_red (^ctx_empty) ^state_ver1 ^state_ver2  ``,
STMT_SIMP >>
EXISTS_TAC``[] : frame_list `` >>
EXP_SIMP
);


val frame_ver3 = `` [(funn_name "f", stmt_empty , ^scopelist2 )] : frame_list `` ;
val state_ver3 = ``(^scopelist14, (^frame_ver3) , empty_ctrl, ^R): state``;


(* test 2: transition for stmt verify T e -> empty*)
val test_stmt_verify2 =
prove(`` stmt_red (^ctx_empty) ^state_ver2 ^state_ver3 ``,
STMT_SIMP
);




val frame_ver4 = `` [(funn_name "f", ^prog_ver3 , ^scopelist2 )] : frame_list `` ;
val state_ver4 = ``(^scopelist14, (^frame_ver4) , empty_ctrl, ^R): state``;

val frame_ver5 = `` [(funn_name "f", ^prog_ver4 , ^scopelist2 )] : frame_list `` ;
val state_ver5 = ``(^scopelist14, (^frame_ver5) , empty_ctrl, ^R): state``;

(* test 3: transition for stmt verify e e -> verify F e*)
val test_stmt_verify3 =
prove(`` stmt_red (^ctx_empty) ^state_ver4 ^state_ver5  ``,
STMT_SIMP >>
EXISTS_TAC``[] : frame_list `` >>
EXP_SIMP >>
EVAL_TAC
);


val frame_ver6 = `` [(funn_name "f", ^prog_ver5 , ^scopelist2 )] : frame_list `` ;
val state_ver6 = ``(^scopelist14, (^frame_ver6) , empty_ctrl, ^R): state``;


(* test 4: transition for stmt verify F e -> parserError = errmsg ; trans rej*)
val test_stmt_verify4 =
prove(`` stmt_red (^ctx_empty) ^state_ver5 ^state_ver6 ``,
STMT_SIMP
);



(*Testing verify_4 the whole execustion SEQ*)

val prog_ver6 =  ``stmt_seq stmt_empty (stmt_trans (e_v (v_str "reject")))``;
val prog_ver7 =  ``(stmt_trans (e_v (v_str "reject")))``;

val frame_ver8 = `` [(funn_name "f", ^prog_ver5 , ^scopelist15 )] : frame_list `` ;
val state_ver8 = ``(^scopelist14, (^frame_ver8) , empty_ctrl, ^R): state``;

val frame_ver9 = `` [(funn_name "f", ^prog_ver6 , ^scopelist16 )] : frame_list `` ;
val state_ver9 = ``(^scopelist14, (^frame_ver9) , empty_ctrl, ^R): state``;

val frame_ver10 = `` [(funn_name "f", ^prog_ver7 , ^scopelist16 )] : frame_list `` ;
val state_ver10 = ``(^scopelist14, (^frame_ver10) , empty_ctrl, ^R): state``;

val frame_ver11 = `` [(funn_name "f", stmt_empty , ^scopelist16 )] : frame_list `` ;
val state_ver11 = ``(^scopelist14, (^frame_ver11) , empty_ctrl, ^Parse_Rej): state``;

val test_stmt_verifyFULL =
prove(`` (stmt_red (^ctx_empty) ^state_ver8 ^state_ver9)
    /\  (stmt_red (^ctx_empty) ^state_ver9 ^state_ver10)
    /\  (stmt_red (^ctx_empty) ^state_ver10 ^state_ver11)
``,
 STMT_SIMP >>
 EXISTS_TAC``[] : frame_list `` >>
 EXISTS_TAC``stmt_empty`` >>
 EXISTS_TAC``^scopelist16`` >>
 EVAL_TAC >>
 STMT_SIMP >>
 DISJ1_TAC >>
 EXISTS_TAC``^scopelist14++^scopelist16`` >>
 EVAL_TAC>>
 FULL_SIMP_TAC list_ss [FUPDATE_EQ]
);




(*** stmt seq  statement reduction --concrete values -- ***)
val prog_seq1  = ``(stmt_declare (t_base bt_bit)  "x"  NONE)``;
val prog_seq2  = ``(stmt_ass (lval_varname (varn_name"x")) (e_v (v_bit ([F], 1))))``;
val prog_seq3 =  ``(stmt_seq ^prog_seq1 ^prog_seq2)``;
val prog_seq4 =  ``(stmt_seq stmt_empty ^prog_seq2)``;

val frame_seq1 = `` [(funn_name "f", ^prog_seq3 , ^scopelist10 )] : frame_list `` ;
val state_seq1 = ``(^scopelist14, (^frame_seq1) , empty_ctrl, ^R): state``;


val frame_seq2 = `` [(funn_name "f", ^prog_seq4 , ^scopelist13 )] : frame_list `` ;
val state_seq2 = ``(^scopelist14, (^frame_seq2) , empty_ctrl, ^R): state``;


(* test 1: transition for    seq dec ; x = F -> seq empty ; x= F *)
val test_stmt_seq1 =
prove(`` stmt_red (^ctx_empty) ^state_seq1 ^state_seq2 ``,
STMT_SIMP >>
RW_TAC (srw_ss()) [Once stmt_red_cases] >>
EVAL_TAC
);


(* test 2: transition for    seq empty ; x= F -> x = F*)
val frame_seq3 = `` [(funn_name "f", ^prog_seq2 , ^scopelist13 )] : frame_list `` ;
val state_seq3 = ``(^scopelist14, (^frame_seq3) , empty_ctrl, ^R): state``;

val test_stmt_seq2 =
prove(`` stmt_red (^ctx_empty) ^state_seq2 ^state_seq3  ``,
STMT_SIMP 
);





(*** lookup expression  reduction --concrete values -- ***)

(* test 1: lookup e current frames stack while global empty*)
val test_e_lookup1 =
prove(`` e_red  (^ctx_empty) [FEMPTY;FEMPTY] ^scopelist8
               (e_var (varn_name"x")) (e_v (v_bit ([F],1))) ([]) ``,
NTAC 2 EXP_SIMP
);

(* test 2: lookup e current frames stack while global non empty*)
val test_e_lookup2 =
prove(`` e_red  (^ctx_empty) ^scopelist3 ^scopelist8
               (e_var (varn_name"x")) (e_v (v_bit ([F],1))) ([]) ``,
NTAC 2 EXP_SIMP
);


(* test 3: lookup varn_star current frames stack while global non empty*)
val test_e_lookup3 =
prove(`` e_red  (^ctx_empty) [FEMPTY;FEMPTY] ^scopelist27
               (e_var (varn_star)) (e_v (v_bit ([F; F],2))) ([]) ``,
NTAC 2 EXP_SIMP
);





(*** more on assignment null  ***)
val prog_null1   = ``stmt_ass lval_null (e_v (v_bit ([T],1)))``;


val frame_null1 = `` [(funn_name "f", ^prog_null1 , ^scopelist7 )] : frame_list `` ;
val state_null1 = ``(^scopelist18, (^frame_null1) , empty_ctrl, ^R): state``;

val frame_null2 = `` [(funn_name "f", stmt_empty , ^scopelist7 )] : frame_list `` ;
val state_null2 = ``(^scopelist18, (^frame_null2) , empty_ctrl, ^R): state``;


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
val ctx1 = ``(FEMPTY, FEMPTY, ^func_sig1, FEMPTY):ctx``;

val prog_call1 = ``(e_call (funn_name "Add1") [e_var (varn_name"x")]) ``;
val prog_call2 = ``(e_call (funn_name "Add1") [(e_v (v_bit ([F],1)))]) ``;

(* test 1: test exp red : call Add1 (x) ~> call Add1 (1)
where the arg is IN i.e. not copied in*)

val test_COPYIN1 =
prove(`` e_red  (^ctx1) ^scopelist7 [FEMPTY]
           (^prog_call1)
	   (^prog_call2)  ([]) ``,
EXP_SIMP >>
EXISTS_TAC ``[( e_var( varn_name "x"), (e_v (v_bit ([F],1))) , "y" , d_in)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([F],1)))`` >>
EXP_SIMP >>
EVAL_TAC
);





(* test 2: test exp red : call Add1 (x) ~> call Add1 (1)
where the arg is IN i.e. not copied in*)

val func_sig2 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_none)] ))): func_map``;
val ctx2 = ``(FEMPTY, FEMPTY, ^func_sig2, FEMPTY):ctx``;

val test_COPYIN2 =
prove(`` e_red  (^ctx2) ^scopelist7 [FEMPTY]
           (^prog_call1)
	   (^prog_call2)  ([]) ``,
EXP_SIMP >>
EXISTS_TAC ``[( e_var ( varn_name "x"), (e_v (v_bit ([F],1))) , "y" , d_none)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([F],1)))`` >>
EXP_SIMP >>
EVAL_TAC
);




(* test 3: test exp red : call Add1 (y, x) ~> call Add1 (y ,1)
where y is OUT so it is copied out, thus we do not evaluate it in the first swipe
and   x is IN so it will be the first value to evaluate and not copied in *)

val func_sig3 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_out); ("b", d_in)] )))``;
val ctx3 = ``(FEMPTY, FEMPTY, ^func_sig3, FEMPTY):ctx``;
val prog_call3 = ``(e_call (funn_name "Add1") [e_var (varn_name "y"); e_var (varn_name "x")]) ``; (*call the function with x,y*)
val prog_call4 = ``(e_call (funn_name "Add1") [e_var (varn_name "y"); (e_v (v_bit ([F],1)))]) ``;


val test_COPYIN3 =
prove(`` e_red (^ctx3) ^scopelist7 [FEMPTY]
           (^prog_call3)
	   (^prog_call4)  ([])``,
	   
EXP_SIMP >>
EXISTS_TAC ``[( e_var (varn_name "y"), e_var (varn_name "y") , "a" , d_out);
              ( e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "b" , d_in)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([F],1)))`` >>
EXP_SIMP >>
EVAL_TAC 
);



(* test 4: test exp red : call Add1 (x, y) ~> call Add1 (1 ,y)
where x is NONE so it is not copied out, thus we do evaluate it in the first swipe
and   y is OUT  *)

val func_sig4 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_out)] )))``;
val ctx4 = ``(FEMPTY, FEMPTY, ^func_sig4, FEMPTY):ctx``;
val prog_call5 = ``(e_call (funn_name "Add1") [ e_var (varn_name "x"); e_var (varn_name "y")]) ``; (*call the function with a,b*)
val prog_call6 = ``(e_call (funn_name "Add1") [(e_v (v_bit ([F],1))); e_var (varn_name "y")]) ``;


val test_COPYIN4 =
prove(``e_red (^ctx4) ^scopelist7 [FEMPTY]
           (^prog_call5)
	   (^prog_call6)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[( e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var (varn_name "y"), e_var (varn_name "y") , "b" , d_out)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([F],1)))`` >>
EXP_SIMP >>
EVAL_TAC 
);



(* test 5 + 6: two arguments call NONE and IN reduction sequence*)
val func_sig5 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_in)] )))``;
val ctx5 = ``(FEMPTY, FEMPTY, ^func_sig5, FEMPTY):ctx``;


val prog_call7 = ``(e_call (funn_name "Add1") [ e_var (varn_name "x") ; e_var (varn_name "y")]) ``; 
val prog_call8 = ``(e_call (funn_name "Add1") [(e_v (v_bit ([F],1))); e_var (varn_name "y")]) ``;
val prog_call9 = ``(e_call (funn_name "Add1") [(e_v (v_bit ([F],1))); (e_v (v_bit ([T],1)))]) ``;


val test_COPYIN5 =
prove(`` e_red (^ctx5) ^scopelist17 [FEMPTY]
           (^prog_call7)
	   (^prog_call8)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[(e_var (varn_name "x"),(e_v (v_bit ([F],1))) , "a" , d_none);
              (e_var (varn_name "y"),e_var (varn_name "y"), "b" , d_in)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([F],1)))`` >>
EXP_SIMP >>
EVAL_TAC 
);



val test_COPYIN6 =
prove(`` e_red (^ctx5) ^scopelist17 [FEMPTY]
           (^prog_call8)
	   (^prog_call9)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1))),(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var (varn_name "y"),(e_v (v_bit ([T],1))) , "b" , d_in)]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC `` (e_v (v_bit ([T],1)))`` >>
EXP_SIMP >>
EVAL_TAC 
);



(* test 7: one arg red with expression operation*)

val prog_call10 = ``(e_call (funn_name "Add1") [e_binop (e_var (varn_name "x")) binop_add (e_var (varn_name "y"))]) ``; 
val prog_call11 = ``(e_call (funn_name "Add1") [e_binop (e_v (v_bit ([F],1))) binop_add  (e_var (varn_name "y"))]) ``; 
val func_sig6 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_in)] )))``;
val ctx6 = ``(FEMPTY, FEMPTY, ^func_sig6, FEMPTY):ctx``;

val test_COPYIN7 =
prove(`` e_red (^ctx6) ^scopelist17 [FEMPTY]
           (^prog_call10)
	   (^prog_call11)  ([])``,
EXP_SIMP >>
EXISTS_TAC ``[(e_binop  (e_var (varn_name "x")) binop_add  (e_var (varn_name "y"))),
               e_binop (e_v (v_bit ([F],1))) binop_add  (e_var (varn_name "y"))
	       , "a"
	       , d_in]`` >>
EVAL_TAC >>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``e_binop (e_v (v_bit ([F],1))) binop_add (e_var (varn_name "y"))`` >>
REPEAT (EXP_SIMP >>
EVAL_TAC) 
);




(****copy_in OUT values aka func_call_newframe rule ****)
(* test 8: copy_in IN values aka func_call_newframe rule*)

val func_sig7 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_in)] )))``;
val ctx7 = ``(FEMPTY, FEMPTY, ^func_sig7, FEMPTY):ctx``;

val prog_call12 = ``(e_call (funn_name "Add1") [(e_v (v_bit ([F],1)))]) ``;


val test_NEWFRAME1 =
prove(`` e_red (^ctx7) ^scopelist7 [FEMPTY]
                  (^prog_call12) 
                  (e_var varn_star) [(funn_name "Add1", stmt_empty , ^scopelist10 )]``,

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
val ctx8 = ``(FEMPTY, FEMPTY, ^func_sig8, FEMPTY):ctx``;

val prog_call13 = ``(e_call (funn_name "Add1") [e_var (varn_name "x")]) ``;

(*FAILS*)
val test_NEWFRAME2 =
prove(`` e_red (^ctx8) ^scopelist7 [FEMPTY]
                  (^prog_call13) 
                  (e_var varn_star) [(funn_name "Add1", stmt_empty , ^scopelist25 )]``,

EXP_SIMP >>
EXISTS_TAC ``[( (e_var (varn_name "x"))
	       , "y"
	       , d_out)]`` >>	       	       
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);


(****copy_in two args IN and OUT values aka func_call_newframe rule ****)
(* test 10: copy_in two arguments (NONE, OUT) values aka func_call_newframe rule*)
val ctx9 = ``(FEMPTY, FEMPTY, ^func_sig4, FEMPTY):ctx``;

val test_NEWFRAME3 =
prove(`` e_red (^ctx4) ^scopelist7 ^scopelist12
                  (^prog_call6) 
                   (e_var varn_star) [(funn_name "Add1", stmt_empty , ^scopelist21 )] ``,
		  
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
val prog_app3 = ``stmt_ass lval_null   (e_call (funn_name "NoAction") [])``;

val table_map1 = ``(FEMPTY |+ ("check_ttl", (e_var(varn_name ("headers.ip.ttl")) , mk_exact)))``;

val ctrl1 = Define
`
 ctrl1 (("check_ttl"), (v_bit ([F; F],2)), (mk_exact)) = SOME  ("Send_to_cpu",[]:e list ) /\
 ctrl1 (("check_ttl"), (v_bit ([T; F],2)) , (mk_exact)) = SOME ("NoAction",[]:e list )
`;

val ctx11 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1):ctx``;


(* test 1: test two reductions app e -> app v -> null := call f     *)

val frame_app1 = `` [(funn_name "f", ^prog_app1 , ^scopelist4 )] : frame_list `` ;
val state_app1 = ``(^scopelist22, (^frame_app1) , ctrl1, ^R): state``;

val frame_app2 = `` [(funn_name "f", ^prog_app2 , ^scopelist4 )] : frame_list `` ;
val state_app2 = ``(^scopelist22, (^frame_app2) , ctrl1, ^R): state``;

val frame_app3 = `` [(funn_name "f", ^prog_app3 , ^scopelist4 )] : frame_list `` ;
val state_app3 = ``(^scopelist22, (^frame_app3) , ctrl1, ^R): state``;


val test_APPLY1 =
prove(``
(stmt_red ^ctx11 ^state_app1 ^state_app2) /\
(stmt_red ^ctx11 ^state_app2 ^state_app3)  ``,

CONJ_TAC >|[
STMT_SIMP>>
NTAC 2 EXP_SIMP>>
EVAL_TAC
,
NTAC 2 (RW.ONCE_RW_TAC[stmt_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [ctrl1])
]);



(* test 2: test two reductions app e -> app v -> null := call f
Where teh value is repeated in teh global and in the local stack scope *)


val ctrl2 = Define
`
 ctrl2 (("check_ttl"), (v_bit ([F],1)), (mk_exact)) = SOME ("Send_to_cpu",[]:e list ) /\
 ctrl2 (("check_ttl"), (v_bit ([],1)), (mk_exact)) = SOME ("NoAction"   ,[]:e list )
`;


val prog_app4 = ``stmt_app "check_ttl" (e_v (v_bit ([F],1))) ``;
val prog_app5 = ``stmt_ass lval_null   (e_call (funn_name "Send_to_cpu") [])``;

val frame_app4 = `` [(funn_name "f", ^prog_app1 , ^scopelist23 )] : frame_list `` ;
val state_app4 = ``(^scopelist22, (^frame_app4) , ctrl2 , ^R): state``;

val frame_app5 = `` [(funn_name "f", ^prog_app4 , ^scopelist23 )] : frame_list `` ;
val state_app5 = ``(^scopelist22, (^frame_app5) , ctrl2 , ^R): state``;

val frame_app6 = `` [(funn_name "f", ^prog_app5 , ^scopelist23 )] : frame_list `` ;
val state_app6 = ``(^scopelist22, (^frame_app6) , ctrl2 , ^R): state``;


val ctx12 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1):ctx``;

val test_APPLY2 =
prove(``
(stmt_red ^ctx12 ^state_app4 ^state_app5) /\
(stmt_red ^ctx12 ^state_app5 ^state_app6) ``,

CONJ_TAC >|[
STMT_SIMP>>
NTAC 2 EXP_SIMP>>
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
val ctx13 = ``(FEMPTY, FEMPTY, ^func_sig10, FEMPTY):ctx``;

val prog_ret1 = ``(stmt_ass (lval_varname (varn_name"g")) (e_call (funn_name "Add1") [e_var (varn_name "x")]))  ``;
val prog_ret2a = ``(stmt_ret (e_v (v_bit ([F;F],2)))) ``;
val prog_ret2b = ``(stmt_ass (lval_varname (varn_name"g"))  (e_var varn_star))  ``;

val frame_ret1 = `` [(funn_name "f", ^prog_ret1 , ^scopelist17 )] : frame_list `` ;
val state_ret1 = ``(^Gscope_list , (^frame_ret1) , empty_ctrl, ^R): state``;

val frame_ret2a = `` [(funn_name "Add1", ^prog_ret2a , ^scopelist25 )] : frame_list `` ;
val frame_ret2b = `` [(funn_name "f", ^prog_ret2b , ^scopelist17 )] : frame_list `` ;

val state_ret2 = ``(^Gscope_list , ((^frame_ret2a)++(^frame_ret2b)) , empty_ctrl, ^R): state``;


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

val frame_ret2a = `` [(funn_name "Add1", ^prog_ret2a , ^scopelist25 )] : frame_list `` ;
val frame_ret2b = `` [(funn_name "f", ^prog_ret2b , ^scopelist28 )] : frame_list `` ;

val state_ret2 = ``(^Gscope_list , ((^frame_ret2a)++(^frame_ret2b)) , empty_ctrl, ^R): state``;


val frame_ret3a = `` [(funn_name "Add1", stmt_empty , ^scopelist25 )] : frame_list `` ;
val frame_ret3b = `` [(funn_name "f", ^prog_ret2b , ^scopelist28 )] : frame_list `` ; (*same as 2a*)
val state_ret3 = ``(^Gscope_list , ((^frame_ret3b)) , empty_ctrl, ^R ) : state``;


val test_return2 =
prove(`` stmt_red ^ctx13 ^state_ret2 ^state_ret3 
``,
FULL_SIMP_TAC list_ss [Once stmt_red_cases ] >>
DISJ2_TAC >>
EXISTS_TAC `` [("y",d_out)]`` >>
EXISTS_TAC ``stmt_empty`` >>
EXISTS_TAC ``(v_bit ([F; F],2))`` >>
EXISTS_TAC ``stmt_ret (e_v (v_bit ([F; F],2)))`` >>
EXISTS_TAC ``[FEMPTY;FEMPTY]: g_scope_list`` >>
STMT_SIMP >>
ASSUME_TAC (finite_mapLib.fupdate_NORMALISE_CONV
``FEMPTY |+ ("y",v_bit ([T],1),NONE) |+ ("x",v_bit ([F],1),NONE) |+
   ("star",v_bit ([F; F],2),NONE) |+ ("x",v_bit ([F],1),NONE)``) >>
fs [FUPDATE_COMMUTES]
);




(* test 3:
test reduction [Add1, ret 0 , cpins] ++ [ f, g := * , oldf] -> [f, g = * , oldf']
without copyouts
Here in this test the frame of the callee is empty while the frame of the caller doesn't change
because the star already has
*)

val frame_ret4a = `` [(funn_name "Add1", ^prog_ret2a , [FEMPTY] )] : frame_list `` ;
val frame_ret4b = `` [(funn_name "f", ^prog_ret2b , ^scopelist28 )] : frame_list `` ;
val state_ret4 = ``(^Gscope_list , ((^frame_ret4a)++(^frame_ret4b)) , empty_ctrl, ^R): state``;

val frame_ret5b = `` [(funn_name "f", ^prog_ret2b , ^scopelist28 )] : frame_list `` ; 
val state_ret5 = ``(^Gscope_list , ((^frame_ret5b)) , empty_ctrl, ^R ) : state``;


val test_return3 =
prove(`` stmt_red ^ctx7 ^state_ret4 ^state_ret5 
``,

FULL_SIMP_TAC list_ss [Once stmt_red_cases ] >>
DISJ2_TAC >> 


EXISTS_TAC `` [("y",d_in)]`` >>
EXISTS_TAC ``stmt_empty`` >>
EXISTS_TAC ``(v_bit ([F; F],2))`` >>
EXISTS_TAC ``stmt_empty`` >>
EXISTS_TAC ``[FEMPTY;FEMPTY]: g_scope_list`` >>

STMT_SIMP >>
ASSUME_TAC (finite_mapLib.fupdate_NORMALISE_CONV
``FEMPTY |+ (varn_name "y",v_bit ([T],1),NONE) |+
   (varn_name "x",v_bit ([F],1),NONE) |+ (varn_star,v_bit ([F; F],2),NONE)``) >>
fs [FUPDATE_COMMUTES]

);



(**************************************************************)
(***    Testing comp reductions --concrete values--       ***)
(**************************************************************)

(* test 1:
test reduction [Add1, empty; ret 0 , cpins] ++ [ f, g := * , oldf] ->
     	       [Add1, ret 0 , cpins] ++ [ f, g := * , oldf]
*)

val frame_comp1a = `` [(funn_name "Add1", stmt_seq stmt_empty ^prog_ret2a , [FEMPTY] )] : frame_list `` ;
val frame_comp1b = `` [(funn_name "f", ^prog_ret2b , ^scopelist28 )] : frame_list `` ;
val state_comp1 = ``(^Gscope_list , ((^frame_comp1a)++(^frame_comp1b)) , empty_ctrl, ^R): state``;


val frame_comp2a = `` [(funn_name "Add1", ^prog_ret2a , [FEMPTY] )] : frame_list `` ; 
val state_comp2 = ``(^Gscope_list , ((^frame_comp2a)++(^frame_comp1b)) , empty_ctrl, ^R): state``;


val test_comp1 =
prove(`` stmt_red ^ctx7 ^state_comp1 ^state_comp2 
``,

FULL_SIMP_TAC list_ss [Once stmt_red_cases ] >>
EXISTS_TAC ``^frame_comp2a`` >>
STMT_SIMP 
);



(****************************************************************)
(***    Testing select value from a rec   --concrete values-- ***)
(****************************************************************)

val select_list1 = `` [((v_bit ([T;T],2)), "tcp"  );
                 ((v_bit ([F;F],2)), "tryudp");
		 ((v_bit ([T],1)), "accept")]
		 ``;

val prog_sel1 = ``e_select
		 (e_binop (e_v (v_bit([F;T],2))) binop_add (e_v (v_bit([F;T],2))))
		 ^select_list1
		 "ack"``;

val prog_sel2 = ``e_select
                  (e_v (v_bit([T;F],2)))
		  ^select_list1
		  "ack"``;

val prog_sel3 = ``e_select
                  (e_v (v_bit([F;F],2)))
		  ^select_list1
		  "ack"``;

(*test1: test (e_select binop list x ) -> (e_select v list x ) *)
val test_select1 =
prove(`` e_red (^ctx3) ^scopelist18 [FEMPTY]
           (^prog_sel1)
	   (^prog_sel2)  ([])``,
NTAC 2 EXP_SIMP >>
EVAL_TAC
);


(*test2: test  (e_select v list x ) -> (x)  DEFAULT*)
val test_select2 =
prove(`` e_red (^ctx3) ^scopelist18 [FEMPTY]
           (^prog_sel2)
	   (e_v (v_str("ack")))  ([])``,
NTAC 2 EXP_SIMP >>
EVAL_TAC
);


(*test3: test  (e_select v list x ) -> (x)  NOT DEFAULT*)
val test_select3 =
prove(`` e_red (^ctx3) ^scopelist18 [FEMPTY]
           (^prog_sel3)
	   (e_v (v_str("tryudp")))  ([])``,
NTAC 2 EXP_SIMP
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


val frame_ass_h1 = `` [(funn_name "f", ^prog_ass_h1 , ^scopelist_h1 )] : frame_list `` ;
val state_ass_h1 = ``(^Gscope_list , (^frame_ass_h1) , empty_ctrl, ^R): state``;

val frame_ass_h2 = `` [(funn_name "f", stmt_empty , ^scopelist_h2 )] : frame_list `` ;
val state_ass_h2 = ``(^Gscope_list , (^frame_ass_h2) , empty_ctrl, ^R): state``;


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



val frame_ass_h3 = `` [(funn_name "f", ^prog_ass_h3 , ^scopelist_h2 )] : frame_list `` ;
val state_ass_h3 = ``(^Gscope_list , (^frame_ass_h3) , empty_ctrl, ^R): state``;


val frame_ass_h4 = `` [(funn_name "f", stmt_empty , ^scopelist_h3 )] : frame_list `` ;
val state_ass_h4 = ``(^Gscope_list , (^frame_ass_h4) , empty_ctrl, ^R): state``;


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



(*test e_h_acc on the reduction   acc header f -> (e_v v) *)
val test_acc_h1 =
prove(`` e_red (^ctx_empty) [FEMPTY;FEMPTY] ^scopelist_h1
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


val frame_ass_s1 = `` [(funn_name "f", ^prog_ass_s1 , ^scopelist_s1 )] : frame_list `` ;
val state_ass_s1 = ``(^Gscope_list , (^frame_ass_s1) , empty_ctrl, ^R): state``;

val frame_ass_s2 = `` [(funn_name "f", stmt_empty , ^scopelist_s2 )] : frame_list `` ;
val state_ass_s2 = ``(^Gscope_list , (^frame_ass_s2) , empty_ctrl, ^R): state``;


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
prove(`` e_red  (^ctx_empty) [FEMPTY; FEMPTY] ^scopelist_s1
                  ^prog_acc_s1 ^prog_acc_s2 ([])
``,
NTAC 2 EXP_SIMP
);




(****************************************************************)
(***    Testing concat two expressions of bit strings         ***)
(****************************************************************)

val prog_conc1 = ``e_concat (e_var( varn_name "x")) (e_var( varn_name "y"))  ``;
val prog_conc2 = ``e_concat (mk_e 0) (e_var( varn_name "y")) ``;
val prog_conc3 = ``e_concat (mk_e 0) (mk_e 1) ``;

(* test1:  e_concat ex ey ->  e_concat v ey*)

val test_conc1 =
prove(`` e_red  (^ctx_empty) ^scopelist17 ^scopelist1
                  ^prog_conc1 ^prog_conc2 ([])
``,
NTAC 3 EXP_SIMP
);


(* test2:  e_concat v ey -> e_concat  v v2 *)
val test_conc2 =
prove(`` e_red  (^ctx_empty) ^scopelist17 ^scopelist1
                  ^prog_conc2 ^prog_conc3 ([])
``,
NTAC 3 EXP_SIMP
);


(* test3:  e_concat v v2 ->  v3 *)

val test_conc3 =
prove(`` e_red  (^ctx_empty) ^scopelist17 ^scopelist1
                  ^prog_conc3 (e_v (v_bit ([F;T],2))) ([])
``,
NTAC 3 EXP_SIMP
);


(****************************************************************)
(***    Testing slice two expressions of bit strings         ***)
(****************************************************************)

val prog_slice1 = ``e_slice (e_var( varn_name "headers.ip.ttl")) (mk_e 0) (mk_e 0)  ``;
val prog_slice2 = ``e_slice (mk_e 2) (mk_e 0) (mk_e 0)  ``;
val prog_slice3 = ``(mk_e 1) ``;

val prog_slice4 = ``e_slice (mk_e 11) (mk_e 1)  (mk_e 1) ``;
val prog_slice5 = `` (mk_e 0) ``;

val prog_slice6 = ``e_slice  (mk_e 8)  (mk_e 3)  (mk_e 0)  ``;
val prog_slice7 = `` (mk_e 8) ``;


val test_slice1 =
prove(`` e_red  (^ctx_empty) ^scopelist22 ^scopelist1
                  ^prog_slice1 ^prog_slice2 ([])
``,
NTAC 3 EXP_SIMP
);



val test_slice2 =
prove(`` e_red  (^ctx_empty) ^scopelist22 ^scopelist1
                  ^prog_slice2 ^prog_slice3 ([])
``,
NTAC 2 EXP_SIMP
);



val test_slice3 =
prove(`` e_red  (^ctx_empty) ^scopelist22 ^scopelist1
                  ^prog_slice4 ^prog_slice5 ([])
``,
NTAC 3 EXP_SIMP
);



val test_slice4 =
prove(`` e_red  (^ctx_empty) ^scopelist22 ^scopelist1
                  ^prog_slice6 ^prog_slice7 ([])
``,
NTAC 3 EXP_SIMP
);



