open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open blastLib bitstringLib;
open p4Theory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;

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


(*mappings from one variable to a tuple (value, string option)*)
val map0  = ``("x", (^bitE , NONE: string option))``;
val map1  = ``("x", (^bitT , NONE: string option))``;
val map2  = ``("x", (^bitF , NONE: string option))``;
val map3  = ``("y", (^bitE , NONE: string option))``;
val map4  = ``("y", (^bitT , NONE: string option))``;
val map5  = ``("y", (^bitF , NONE: string option))``;
val map6  = ``("z", (^bitE , NONE: string option))``;
val map7  = ``("z", (^bitT , NONE: string option))``;
val map8  = ``("z", (^bitF , NONE: string option))``;
val map9  = ``("x", (^bitA , NONE: string option))``;
val map10 = ``("x", (^bitA , NONE: string option))``;
val map11 = ``("parseError", (^bitErr1 , NONE: string option))``;
val map12 = ``("parseError", (^bitErr2 , NONE: string option))``;
val map13  = ``("y", (^bitF , SOME "x"))``;
val map14 = ``("headers.ip.ttl", (^bitTwo, NONE:string option)) ``;
val map15  = ``("a", (^bitF , NONE: string option))``;
val map16  = ``("b", (^bitF , SOME "y"))``;
val map17 = ``("headers.ip.ttl", (^bitF, NONE:string option)) ``;


(*scopes examples*)
val scope0 = ``(FEMPTY |+ ^map0)``;
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
val scope17 = ``(FEMPTY |+ ^map15)``;
val scope18 = ``(FEMPTY |+ ^map17)``;

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

(*empty ctrl*)
val empty_ctrl =
Define
`empty_ctrl (" ", v, match_kind_exact) = NONE:(string # e list) option`;


(*context examples*)
val ctx_empty = ``(FEMPTY, FEMPTY, FEMPTY, FEMPTY, empty_ctrl):ctx``;


(*** assignment statement reduction --concrete values -- ***)
val state1  = ``(state_tup (stacks_tup ^scopelist1 []) ^R): state``;
val state2  = ``(state_tup (stacks_tup ^scopelist2 []) ^R): state``;
val state2b = ``(state_tup (stacks_tup ^scopelist6 []) ^R): state``;
val state2c = ``(state_tup (stacks_tup ^scopelist17 []) ^R): state``;
val state2d = ``(state_tup (stacks_tup ^scopelist4 []) ^R): state``;

val prog1  = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([T], 1))))``;
val prog2  = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([F], 1))))``;
val exp1   = ``(e_binop (e_v (v_bit ([T],1))) binop_add (e_v (v_bit ([F],1))))``;
val prog2c = ``(stmt_ass (lval_varname "x") (^exp1) )``; (*assign with reduction*)
val prog2d = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([T],1))) )``; 
val prog2e = ``(stmt_ass (lval_varname "x") (e_var("y") ))``;

val test_stmt_ass1 =
prove(`` stmt_red ^ctx_empty (^prog1) 
                  (^state1)
                  stmt_empty
                  (^state2)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]
);


val test_stmt_ass2 =
prove(`` stmt_red (^ctx_empty) (^prog2) 
                  (^state2)
                  stmt_empty
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]
);


val test_stmt_ass3 =
prove(`` stmt_red (^ctx_empty) (^prog2) 
                  (^state2b)
                  stmt_empty
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]
);



val test_stmt_ass4 =
prove(`` stmt_red (^ctx_empty) (^prog2c) 
                  (^state1)
                  (^prog2d)
                  (^state1)  ``,
REPEAT(RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);


val test_stmt_ass5 =
prove(`` stmt_red (^ctx_empty) (^prog2e) 
                  (^state2c)
                  (^prog2d)
                  (^state2c)  ``,
REPEAT(RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);


val test_stmt_ass6 =
prove(`` stmt_red ^ctx_empty (^prog1) 
                  (^state2)
                  stmt_empty
                  (^state2)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]
);


(*** if statement reduction --concrete values --  ***)
val prog3a = ``(stmt_cond (e_v (v_bool  T )) stmt_empty  ^prog2 )``;
val prog4a = ``(stmt_cond (e_v (v_bool  F )) stmt_empty  ^prog2 )``;
val cond1  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([F],1))))``;
val cond2  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([T],1))))``;
val prog3b = ``(stmt_cond  ^cond1 stmt_empty  ^prog2 )``;
val prog4b = ``(stmt_cond  ^cond2 stmt_empty  ^prog2 )``;

val test_stmt_cond1 =
prove(`` stmt_red (^ctx_empty) (^prog3a) 
                  (^state1)
                  stmt_empty
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []
);


val test_stmt_cond2 =
prove(`` stmt_red (^ctx_empty) (^prog4a) 
                  (^state1)
                  (^prog2)
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []
);


val test_stmt_cond3 =
prove(`` stmt_red (^ctx_empty) (^prog3b) 
                  (^state1)
                  (^prog3a)
                  (^state1)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);

val test_stmt_cond4 =
prove(`` stmt_red (^ctx_empty) (^prog4b) 
                  (^state1)
                  (^prog4a)
                  (^state1)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);




(*** declare statement reduction --concrete values -- ***)
val state3 = ``(state_tup (stacks_tup ^scopelist5 []) ^R): state``;
val state4 = ``(state_tup (stacks_tup ^scopelist6 []) ^R): state``;
val prog5  = ``(stmt_declare "x"  (t_base bt_bit) )``;

val test_stmt_decl1 =
prove(`` stmt_red (^ctx_empty) (^prog5) 
                  (^state3)
                  stmt_empty
                  (^state4)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);




val state5 = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;
val state6 = ``(state_tup (stacks_tup ^scopelist13 []) ^R): state``;

val test_stmt_decl2 =
prove(`` stmt_red (^ctx_empty) (^prog5) 
                  (^state5)
                  stmt_empty
                  (^state6)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);


(*** block enter, exec, exit statement reduction --concrete values -- ***)
val state7 = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;
val state8 = ``(state_tup (stacks_tup ^scopelist11 []) ^R): state``;
val state9 = ``(state_tup (stacks_tup ^scopelist12 []) ^R): state``;
val prog6a =  ``(stmt_block ^prog5 )``;
val prog6b =  ``(stmt_block_ip ^prog5)``;
val prog6c =  ``(stmt_block_ip stmt_empty)``;

val test_stmt_block_enter =
prove(`` stmt_red (^ctx_empty)(^prog6a) 
                  (^state7)
                  (^prog6b) 
                  (^state8)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
SIMP_TAC list_ss []  
);


 
val test_stmt_block_exec =
prove(`` stmt_red (^ctx_empty)(^prog6b) 
                  (^state8)
                  (^prog6c) 
                  (^state9)  ``,
REPEAT ( RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )
);


val test_stmt_block_exit =
prove(`` stmt_red (^ctx_empty)(^prog6c) 
                  (^state9)
                  (stmt_empty) 
                  (^state7)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT ( EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )
);



(*** stmt seq  statement reduction --concrete values -- ***)

val prog7a =  ``(stmt_seq ^prog5 ^prog2)``;
val prog7b =  ``(stmt_seq stmt_empty (^prog2))``;
val prog7c =  ``(^prog2)``;
val state7a = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;
val state7b = ``(state_tup (stacks_tup ^scopelist13 []) ^R): state``;
val state7c = ``(state_tup (stacks_tup ^scopelist14 []) ^R): state``;

val test_stmt_seq1 =
prove(`` stmt_red (^ctx_empty) (^prog7a) 
                  (^state7a)
                  (^prog7b) 
                  (^state7b)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);


val test_stmt_seq2 =
prove(`` stmt_red (^ctx_empty) (^prog7b) 
                  (^state7b)
                  (^prog7c) 
                  (^state7b)  ``,

RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 6 DISJ2_TAC >>  DISJ1_TAC >>
EXISTS_TAC``(stacks_tup
         [FEMPTY |+ ("y",v_bit ([F],1),NONE) |+ ("x",v_bit ARB,NONE)] [])`` >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);





(*** transitions stmt reduction --concrete values -- ***)
val prog9a =  ``stmt_trans (e_var "MoveNext") ``;
val prog9b =  ``stmt_empty``;
val prog9c =  ``stmt_trans (e_var "accept") ``;
val prog9d =  ``stmt_trans (e_var "reject") ``;

val state9a = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;
val state9b = ``(state_tup (stacks_tup ^scopelist10 []) (status_pars_next (pars_next_trans "MoveNext"))): state``;
val state9c = ``(state_tup (stacks_tup ^scopelist10 []) ^Parse_Acc): state``;
val state9d = ``(state_tup (stacks_tup ^scopelist10 []) ^Parse_Rej): state``;



val test_stmt_trans1 =
prove(`` stmt_red (^ctx_empty) (^prog9a) 
                  (^state9a)
                  (^prog9b) 
                  (^state9b)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);


val test_stmt_trans2 =
prove(`` stmt_red (^ctx_empty) (^prog9c) 
                  (^state9a)
                  (^prog9b) 
                  (^state9c)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);

val test_stmt_trans3 =
prove(`` stmt_red (^ctx_empty) (^prog9d) 
                  (^state9a)
                  (^prog9b) 
                  (^state9d)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);





(*** verify  statement reduction --concrete values -- ***)

(*Testing verify_e1 verify_e2 with both T and F evaluation *)
val prog8a =  ``stmt_verify (^cond1) (e_v (v_err "PacketTooShort"))``;
val prog8b =  ``stmt_verify (e_v (v_bool  T )) (e_v (v_err "PacketTooShort"))``;
val prog8c =  ``stmt_verify (^cond2) (e_v (v_err "PacketTooShort"))``;
val prog8d =  ``stmt_verify (e_v (v_bool  F )) (e_v (v_err "PacketTooShort"))``;
val prog8e =  ``stmt_empty``;
val prog8f =  ``stmt_seq (stmt_ass (lval_varname "parseError") ((e_v (v_err "PacketTooShort")))) (stmt_trans (e_var"reject"))``;




val state8a = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;
val state8b = ``(state_tup (stacks_tup ^scopelist10 []) ^R): state``;



(*Testing verify_e1*)
val test_stmt_verify1 =
prove(`` stmt_red (^ctx_empty)(^prog8a) 
                  (^state8a)
                  (^prog8b) 
                  (^state8a)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);

val test_stmt_verify2 =
prove(`` stmt_red (^ctx_empty)(^prog8c) 
                  (^state8a)
                  (^prog8d) 
                  (^state8a)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);


(*Testing verify_3*)
val test_stmt_verify3 =
prove(`` stmt_red (^ctx_empty)(^prog8b) 
                  (^state8a)
                  (^prog8e) 
                  (^state8a)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);


(*Testing verify_4 *)

val test_stmt_verify4 =
prove(`` stmt_red (^ctx_empty)(^prog8d) 
                  (^state8a)
                  (^prog8f) 
                  (^state8a)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []  
);


(*Testing verify_4 the whole execustion*)
val prog8g =  ``stmt_seq stmt_empty (stmt_trans (e_var"reject"))``;
val prog8h =  ``(stmt_trans (e_var"reject"))``;
val state10a = ``(state_tup (stacks_tup ^scopelist15 []) ^R): state``;
val state10b = ``(state_tup (stacks_tup ^scopelist16 []) ^R): state``;
val state10c = ``(state_tup (stacks_tup ^scopelist16 []) ^Parse_Rej): state``;


val test_stmt_verify5 =
prove(``(stmt_red (^ctx_empty) (^prog8d) 
                  (^state10a)
                  (^prog8f) 
                  (^state10a))
		  /\
	(stmt_red (^ctx_empty) (^prog8f) 
                  (^state10a)
                  (^prog8g) 
                  (^state10b))
		  /\
	(stmt_red (^ctx_empty) (^prog8g) 
                  (^state10b)
                  (^prog8h) 
                  (^state10b))
		  /\
	 (stmt_red (^ctx_empty) (^prog8h) 
                  (^state10b)
                  (stmt_empty) 
                  (^state10c))	  		  
``,
CONJ_TAC >| [
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
,
CONJ_TAC >| [
NTAC 3 (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [FUPDATE_EQ])
,
CONJ_TAC >| [
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 6 DISJ2_TAC >>  DISJ1_TAC >>
EXISTS_TAC``(stacks_tup
            [FEMPTY |+ ("z",v_bit ([T],1),NONE) |+
             ("parseError",v_err "PacketTooShort",NONE)] [])`` >>
EVAL_TAC
,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
]]]
);




(*** Parser reductions --concrete values -- ***)

val pars_map = ``(FEMPTY |+ ("start", stmt_seq (^prog8b)  (stmt_trans (e_var "p_ipv4")))
                         |+ ("p_ipv4", (^prog2) ))``;

val ctx1 = ``(FEMPTY, FEMPTY, ^pars_map, FEMPTY, empty_ctrl):ctx``;

val state11a = ``(state_tup (stacks_tup ^scopelist2 []) ^R): state``;
val state11b = ``(state_tup (stacks_tup ^scopelist1 []) ^R): state``;
val state11c = ``(state_tup (stacks_tup ^scopelist1 []) ^Parse_Rej): state``;
val state11d = ``(state_tup (stacks_tup ^scopelist1 []) ^Parse_Acc): state``;

val test_pars_sem1 =
prove(`` pars_red (^ctx1) (stmt_seq (^prog8b)  (stmt_trans (e_var "p_ipv4"))) 
                  (^state11a)  
                  (stmt_seq stmt_empty  (stmt_trans (e_var "p_ipv4")))
                  (^state11a) ``,
REPEAT (RW.ONCE_RW_TAC[pars_red_cases, e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);


val test_pars_sem2 =
prove(`` pars_red (^ctx1) (stmt_seq stmt_empty  (stmt_trans (e_var "p_ipv4"))) 
                  (^state11a)  
                  (stmt_trans (e_var "p_ipv4"))
                  (^state11a) ``,
RW.ONCE_RW_TAC[pars_red_cases] >>
DISJ1_TAC >>
EVAL_TAC>>
NTAC 2 (EXISTS_TAC``stacks_tup [FEMPTY |+ ("x",v_bit ([T],1),NONE)] []``) >>
EVAL_TAC>>
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 6 DISJ2_TAC >>  DISJ1_TAC >>
EXISTS_TAC``(stacks_tup [FEMPTY |+ ("x",v_bit ([T],1),NONE)] [])`` >>
EVAL_TAC
);


val test_pars_sem3 =
prove(`` pars_red (^ctx1)(stmt_trans (e_var "p_ipv4"))
                  (^state11a)
		  (^prog2)
                  (^state11a) ``,
NTAC 2 (RW.ONCE_RW_TAC[pars_red_cases, e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []) >>
EVAL_TAC
);



val test_pars_sem4 =
prove(`` pars_red (^ctx1) (^prog2)
                  (^state11a)
		  (stmt_trans (e_var "reject"))
                  (^state11b) ``,
RW.ONCE_RW_TAC[pars_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
NTAC 2 (DISJ2_TAC) >>
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC>>
SIMP_TAC std_ss [FUPDATE_EQ]

);


val test_pars_sem5 =
prove(`` pars_t_red (^ctx1)(stmt_trans (e_var "reject"))
                    (^state11b)
		    (^state11c) ``,
RW.ONCE_RW_TAC[pars_t_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC``stmt_empty`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC
);


(*extra check for accpet*)
val test_pars_sem5 =
prove(`` pars_t_red (^ctx1) (stmt_trans (e_var "accept"))
                  (^state11b)
		  (^state11d) ``,
RW.ONCE_RW_TAC[pars_t_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC``stmt_empty`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []>>
EVAL_TAC
);





(*** lookup expression  reduction --concrete values -- ***)

val state_e1 = ``(stacks_tup (^scopelist8) [])``;

val test_e_lookup =
prove(`` e_red    (^ctx_empty) (e_var "x") 
                  (^state_e1)  (^R)
                  (e_v (v_bit ([F],1))) 
                  (^state_e1)  (^R) ``,
RW.ONCE_RW_TAC[e_red_cases, lookup_vexp_def] >>
NTAC 2 (EVAL_TAC>>
FULL_SIMP_TAC list_ss []  )
);




(*** more on assignment (struct, header field and null)  reduction --concrete values -- ***)
val state12a  = ``(state_tup (stacks_tup ^scopelist7 []) ^R): state``;
val prog10a   = ``stmt_ass lval_null (e_v (v_bit ([T],1)))``;
val prog10b   = ``stmt_ass (lval_field (lval_varname "f") "f") ``;

(*tests of assignment null*)
val test_stmt_ass_null =
prove(`` stmt_red (^ctx1) (^prog10a) 
                  (^state12a)
                  (stmt_empty) 
                  (^state12a) ``,
RW.ONCE_RW_TAC[e_red_cases, lookup_vexp_def] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);

(*TODO: Ask Didrik about the records and header representation?*)



(**************************************************************)
(*** Testing function calls reductions --concrete values -- ***)
(**************************************************************)

(****copy_in IN values aka func_call_args rule ****)

val func_sig1 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_in)] )))``;
val ctx2 = ``(FEMPTY, ^func_sig1, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call1a = ``(e_func_call "Add1" [e_var "x"]) ``;
val prog_call1b = ``(e_func_call "Add1" [(e_v (v_bit ([F],1)))]) ``;
val stacks_call1a  = ``(stacks_tup ^scopelist1 [])``;




val test_COPYIN1 =
prove(`` e_red    (^ctx2)(^prog_call1a) 
                  (^stacks_call1a) (^R)
                  (^prog_call1b) 
                  (^stacks_call1a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var "x", (e_v (v_bit ([F],1))) , "y" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 3 (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);




val func_sig2 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_none)] )))``;
val ctx3 = ``(FEMPTY, ^func_sig2, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_COPYIN2 =
prove(`` e_red    (^ctx3)(^prog_call1a) 
                  (^stacks_call1a) (^R)
                  (^prog_call1b) 
                  (^stacks_call1a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var "x", (e_v (v_bit ([F],1))) , "y" , d_none)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>
RW.ONCE_RW_TAC[e_red_cases] >>
NTAC 3 (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);




(*two arguments call  out in *)
val func_sig3 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_out); ("b", d_in)] )))``;
val ctx4 = ``(FEMPTY, ^func_sig3, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call2a = ``(e_func_call "Add1" [e_var "y"; e_var "x"]) ``; (*call the function with x,y*)
val prog_call2b = ``(e_func_call "Add1" [e_var "y"; (e_v (v_bit ([F],1)))]) ``;


val test_COPYIN3 =
prove(`` e_red    (^ctx4)(^prog_call2a) 
                  (^stacks_call1a) (^R)
                  (^prog_call2b) 
                  (^stacks_call1a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var "y", e_var "y"            , "a" , d_out);
              ( e_var "x",(e_v (v_bit ([F],1))) , "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



(*two arguments call  none out*)
val func_sig4 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_out)] )))``;
val ctx5 = ``(FEMPTY, ^func_sig4, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call3a = ``(e_func_call "Add1" [ e_var "x"; e_var "y"]) ``; (*call the function with a,b*)
val prog_call3b = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); e_var "y"]) ``;


val test_COPYIN4 =
prove(`` e_red    (^ctx5)(^prog_call3a) 
                  (^stacks_call1a) (^R)
                  (^prog_call3b) 
                  (^stacks_call1a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var "x",(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var "y",    e_var"y"          , "b" , d_out)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



(*two arguments call none in with expression operations*)
val func_sig5 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_none); ("b", d_in)] )))``;
val ctx6 = ``(FEMPTY, ^func_sig5, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val stacks_call4a  = ``(stacks_tup ^scopelist17 [])``;
val prog_call4a = ``(e_func_call "Add1" [ e_var "x" ; e_var "y"]) ``; 
val prog_call4b = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); e_var "y"]) ``;
val prog_call4c = ``(e_func_call "Add1" [(e_v (v_bit ([F],1))); (e_v (v_bit ([T],1)))]) ``;

val test_COPYIN5 =
prove(`` e_red   (^ctx6) (^prog_call4a) 
                  (^stacks_call4a) (^R)
                  (^prog_call4b) 
                  (^stacks_call4a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( e_var "x",(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var "y",e_var "y" , "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>


RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



val test_COPYIN6 =
prove(`` e_red    (^ctx6)(^prog_call4b) 
                  (^stacks_call4a) (^R)
                  (^prog_call4c) 
                  (^stacks_call4a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1))),(e_v (v_bit ([F],1))) , "a" , d_none);
              ( e_var "y"            ,(e_v (v_bit ([T],1))) , "b" , d_in)]`` >>
EXISTS_TAC ``(stmt_empty)`` >>

RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);




val prog_call5a = ``(e_func_call "Add1" [e_binop (e_var "x") binop_add (e_var "y")]) ``; 
val prog_call5b = ``(e_func_call "Add1" [e_binop (e_v (v_bit ([F],1))) binop_add (e_var "y")]) ``; 
val func_sig6 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("a",d_in)] )))``;
val ctx7 = ``(FEMPTY, ^func_sig6, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_COPYIN7 =
prove(`` e_red    (^ctx7)(^prog_call5a) 
                  (^stacks_call4a) (^R)
                  (^prog_call5b) 
                  (^stacks_call4a) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[(e_binop (e_var "x") binop_add (e_var "y")),
               e_binop (e_v (v_bit ([F],1))) binop_add (e_var "y")
	       , "a"
	       , d_in]`` >>
EXISTS_TAC ``(stmt_empty)`` >>


NTAC 2(
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
) >>

REPEAT (
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);




val Fn = ``called_function_name_function_name``; 

(****copy_in IN values aka func_call_newframe rule ****)

val func_sig7 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_in)] )))``;
val ctx8 = ``(FEMPTY, ^func_sig7, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call1b = ``(e_func_call "Add1" [(e_v (v_bit ([F],1)))]) ``;
val stacks_call5a  = ``(stacks_tup ^scopelist1 [])``;
val stacks_call5b  = ``(stacks_tup ^scopelist19 [([] , ^Fn "Add1")])``;
(*we can't add (^scopelist1 , ^Fn "Add1") here in the call stack because we are calling from main*)


val test_NEWFRAME1 =
prove(`` e_red    (^ctx8)(^prog_call1b) 
                  (^stacks_call5a) (^R)
                  (e_func_exec stmt_empty) 
                  (^stacks_call5b) (^R)``,

RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>

DISJ2_TAC >> DISJ1_TAC >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1)))
	       , "y"
	       , d_in)]`` >>
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )

);



(****copy_in OUT values aka func_call_newframe rule ****)

val func_sig8 = ``(FEMPTY |+ ("Add1", (stmt_empty , [("y",d_out)] )))``;
val ctx9 = ``(FEMPTY, ^func_sig8, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call6a = ``(e_func_call "Add1" [e_var "x"]) ``;
val stacks_call6a  = ``(stacks_tup ^scopelist1 [])``;
val stacks_call6b  = ``(stacks_tup ^scopelist20 [([] , ^Fn "Add1")])``;

val test_NEWFRAME2 =
prove(`` e_red    (^ctx9)(^prog_call6a) 
                  (^stacks_call6a) (^R)
                  (e_func_exec stmt_empty) 
                  (^stacks_call6b) (^R)``,

RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>

DISJ2_TAC >> DISJ1_TAC >>
EXISTS_TAC ``[( (e_var "x")
	       , "y"
	       , d_out)]`` >>
	       
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )

);



(****copy_in two args IN and OUT values aka func_call_newframe rule ****)
val stacks_call7a  = ``(stacks_tup ^scopelist14 [])``;
val stacks_call7b  = ``(stacks_tup ^scopelist21 [([] , ^Fn "Add1")])``;

val ctx9 = ``(FEMPTY, ^func_sig4, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val test_NEWFRAME3 =
prove(`` e_red    (^ctx9)(^prog_call3b) 
                  (^stacks_call7a) (^R)
                  (e_func_exec stmt_empty) 
                  (^stacks_call7b) (^R)``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``[( (e_v (v_bit ([F],1))) , "a" , d_none);
              (  e_var"y"          , "b" , d_out)]`` >>
EVAL_TAC
);




(*call a function from an other function*)
(*
val func_sig9 = ``(FEMPTY |+ ("Add1",(stmt_ass lval_null (e_func_call "Sub" [e_var "x"])) , [("a",d_in)] ))
                          |+ ("Sub" ,(stmt_empty , [("b",d_none)]))``;

val ctx10 = ``(FEMPTY, ^func_sig9, FEMPTY, FEMPTY, empty_ctrl):ctx``;

val prog_call7a= ``e_func_exec (stmt_ass lval_null (e_func_call "Sub" [e_var "x"]))``;
val prog_call7b= ``e_func_exec (stmt_ass lval_null (e_func_call "Sub" [e_v (v_bit ([F],1))]))``;
val prog_call7c= ``e_func_exec (stmt_ass lval_null (e_func_exec  stmt_empty))``;

val stacks_call8a  = ``(stacks_tup ^scopelist23 [([] , ^Fn "Add1")])``;


val test_NEWFRAME4 =
prove(`` e_red    (^ctx10)(^prog_call7a) 
                  (^stacks_call8a) (^R)
                  (^prog_call7b) 
                  (^stacks_call8a) (^R)``,

RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
*)






(**************************************************************)
(*** Testing apply and tables reductions --concrete values-- ***)
(**************************************************************)
val prog_stmt_apply1 = ``stmt_app "check_ttl" (e_var ("headers.ip.ttl")) ``;
val prog_stmt_apply2 = ``stmt_app "check_ttl" (e_v (v_bit ([T; F],2))) ``;
val prog_stmt_apply3 = ``stmt_ass lval_null   (e_func_call "NoAction" [])``;

val state13a = ``state_tup (stacks_tup (^scopelist22) []) ^R``;

val table_map1 = ``(FEMPTY |+ ("check_ttl", (e_var("headers.ip.ttl") , match_kind_exact)))``;

val ctrl1 = Define
`
 ctrl1 (("check_ttl"), (v_bit ([F; F],2)), (match_kind_exact)) = SOME ("Send_to_cpu",[]:e list ) /\
 ctrl1 (("check_ttl"),          x        , (match_kind_exact)) = SOME ("NoAction",[]:e list )
`;
val ctx11 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1, ctrl1):ctx``;


val test_TABLE1 =
prove(``
(stmt_red (^ctx11)(^prog_stmt_apply1) 
                  (^state13a) 
                  (^prog_stmt_apply2) 
                  (^state13a)) /\


(stmt_red (^ctx11)(^prog_stmt_apply2) 
                  (^state13a) 
                  (^prog_stmt_apply3) 
                  (^state13a)) ``,

NTAC 2 (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []) >>
EVAL_TAC
);





val prog_stmt_apply2b = ``stmt_app "check_ttl" (e_v (v_bit ([F],1))) ``;
val prog_stmt_apply3b = ``stmt_ass lval_null   (e_func_call "Send_to_cpu" [])``;
val state13b = ``state_tup (stacks_tup (^scopelist24) []) ^R``;

val ctrl2 = Define
`
 ctrl2 (("check_ttl"), (v_bit ([F],1)), (match_kind_exact)) = SOME ("Send_to_cpu",[]:e list ) /\
 ctrl2 (("check_ttl"),        x       , (match_kind_exact)) = SOME ("NoAction"   ,[]:e list )
`;


val ctx12 = ``(FEMPTY, FEMPTY, FEMPTY, ^table_map1, ctrl2):ctx``;

val test_TABLE2 =
prove(``
(stmt_red (^ctx12)(^prog_stmt_apply1) 
                  (^state13b) 
                  (^prog_stmt_apply2b) 
                  (^state13b))   /\
		  
(stmt_red (^ctx12)(^prog_stmt_apply2b) 
                  (^state13b) 
                  (^prog_stmt_apply3b) 
                  (^state13b)) ``,

NTAC 2 (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []) >>
EVAL_TAC
);



(**************************************************************)
(***    Testing return reductions --concrete values--       ***)
(**************************************************************)




val func_sig10 = ``(FEMPTY |+ ("Add1", (stmt_ret (e_v (v_bit ([F;F],2))) , [("y",d_out)] )))``;
val ctx9 = ``(FEMPTY, ^func_sig10, FEMPTY, FEMPTY, empty_ctrl):ctx``;
val prog_call9a = ``(e_func_call "Add1" [e_var "x"]) ``;
val prog_call9b = ``(e_func_exec (stmt_ret (e_v (v_bit ([F;F],2))))) ``;

val prog_return1a = ``((stmt_ret (e_v (v_bit ([F;F],2))))) ``;
val prog_return1b = ``(stmt_empty)``;

(*val prog_return1a = ``(e_func_exec (stmt_ret (e_v (v_bit ([F;F],2))))) ``;*)
(*val prog_return1b = ``(e_func_exec stmt_empty) ``;*)

val stacks_call9a  = ``(stacks_tup ^scopelist17 [])``;
val stacks_call9b  = ``(stacks_tup ^scopelist25 [([] , ^Fn "Add1")])``;



val state14a = ``(state_tup (stacks_tup ^scopelist25 [([] , ^Fn "Add1")]) ^R): state``;
val state14b = ``(state_tup (stacks_tup ^scopelist17 [])
                       (status_return  (v_bit ([F;F],2)))):state``;




val test_return1 =
prove(`` (e_red   (^ctx9)(^prog_call9a) 
                  (^stacks_call9a) (^R)
                  (^prog_call9b) 
                  (^stacks_call9b) (^R))

     /\  (e_red    (^ctx9)(^prog_return2a) 
                  (^stacks_call9b) (^R)
                  (^prog_return2b) 
                  (^stacks_call9a) ((status_return  (v_bit ([F;F],2)))))



``,
CONJ_TAC >| [
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
DISJ2_TAC >> DISJ1_TAC >>
EXISTS_TAC ``[( (e_var "x")
	       , "y"
	       , d_out)]`` >>	       
REPEAT (EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )
,
REPEAT(RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [FUPDATE_EQ]) 
]
);



val prog_return2a = ``(e_func_exec (stmt_ret (e_v (v_bit ([F;F],2))))) ``;
val prog_return2b = ``(e_func_exec stmt_empty) ``;

val test_return2 =
prove(`` (stmt_red (^ctx9)(^prog_return1a) 
                  (^state14a)
                  (^prog_return1b) 
                  (^state14b))
``,

RW.ONCE_RW_TAC[e_red_cases] >>
DISJ1_TAC >>
EVAL_TAC>>
EXISTS_TAC ``[(  "y", d_out)]`` >>	       
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] >>
EXISTS_TAC ``"Add1"`` >>
EXISTS_TAC ``stmt_ret (e_v (v_bit ([F; F],2)))`` >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [FUPDATE_EQ]
);











