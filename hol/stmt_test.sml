open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;
     
open p4Theory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;



(*minimalistic bits representations*)
val bitE = ``v_bit ([] ,0)``;
val bitT = ``v_bit ([T],1)``;
val bitF = ``v_bit ([F],1)``;



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

(*** assignment statement reduction --concrete values -- ***)
val state1 = ``(state_tup (stacks_tup ^scopelist1 []) status_running): state``;
val state2 = ``(state_tup (stacks_tup ^scopelist2 []) status_running): state``;
val state2b = ``(state_tup (stacks_tup ^scopelist6 []) status_running): state``;
val prog1 = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([T], 1))))``;
val prog2 = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([F], 1))))``;
val exp1  = ``(e_binop (e_v (v_bit ([T],1))) binop_add (e_v (v_bit ([F],1))))``;
val prog2c = ``(stmt_ass (lval_varname "x") (^exp1) )``; (*assign with reduction*)
val prog2d = ``(stmt_ass (lval_varname "x") (e_v (v_bit ([T],1))) )``; (*assign with reduction*)

val test_stmt_ass1 =
prove(`` stmt_red (^prog1) 
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
prove(`` stmt_red (^prog2) 
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
prove(`` stmt_red (^prog2) 
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
prove(`` stmt_red (^prog2c) 
                  (^state1)
                  (^prog2d)
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
  cheat                                (*TODO: check with Didrik about the simple exp conversions*)
);




(*** if statement reduction --concrete values --  ***)
val prog3a = ``(stmt_cond (e_v (v_bool  T )) stmt_empty  ^prog2 )``;
val prog4a = ``(stmt_cond (e_v (v_bool  F )) stmt_empty  ^prog2 )``;
val cond1  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([F],1))))``;
val cond2  = ``(e_binop (e_v (v_bit ([F],1))) binop_eq (e_v (v_bit ([T],1))))``;
val prog3b = ``(stmt_cond  ^cond1 stmt_empty  ^prog2 )``;
val prog4b = ``(stmt_cond  ^cond2 stmt_empty  ^prog2 )``;

val test_stmt_cond1 =
prove(`` stmt_red (^prog3a) 
                  (^state1)
                  stmt_empty
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []
);


val test_stmt_cond2 =
prove(`` stmt_red (^prog4a) 
                  (^state1)
                  (^prog2)
                  (^state1)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss []
);


val test_stmt_cond3 =
prove(`` stmt_red (^prog3b) 
                  (^state1)
                  (^prog3a)
                  (^state1)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);

val test_stmt_cond4 =
prove(`` stmt_red (^prog4b) 
                  (^state1)
                  (^prog4a)
                  (^state1)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [])
);




(*** declare statement reduction --concrete values -- ***)
val state3 = ``(state_tup (stacks_tup ^scopelist5 []) status_running): state``;
val state4 = ``(state_tup (stacks_tup ^scopelist6 []) status_running): state``;
val prog5 = ``(stmt_declare "x"  (t_base bt_bit) )``;

val test_stmt_decl1 =
prove(`` stmt_red (^prog5) 
                  (^state3)
                  stmt_empty
                  (^state4)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);




val state5 = ``(state_tup (stacks_tup ^scopelist10 []) status_running): state``;
val state6 = ``(state_tup (stacks_tup ^scopelist13 []) status_running): state``;

val test_stmt_decl2 =
prove(`` stmt_red (^prog5) 
                  (^state5)
                  stmt_empty
                  (^state6)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [LUPDATE_def, arb_from_t_def]  
);


(*** block enter, exec, exit statement reduction --concrete values -- ***)
val state7 = ``(state_tup (stacks_tup ^scopelist10 []) status_running): state``;
val state8 = ``(state_tup (stacks_tup ^scopelist11 []) status_running): state``;
val state9 = ``(state_tup (stacks_tup ^scopelist12 []) status_running): state``;
val prog6a =  ``(stmt_block ^prog5 )``;
val prog6b =  ``(stmt_block_ip ^prog5)``;
val prog6c =  ``(stmt_block_ip stmt_empty)``;

val test_stmt_block_enter =
prove(`` stmt_red (^prog6a) 
                  (^state7)
                  (^prog6b) 
                  (^state8)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
SIMP_TAC list_ss []  
);


 
val test_stmt_block_exec =
prove(`` stmt_red (^prog6b) 
                  (^state8)
                  (^prog6c) 
                  (^state9)  ``,
REPEAT ( RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )
);


val test_stmt_block_exec =
prove(`` stmt_red (^prog6c) 
                  (^state9)
                  (stmt_empty) 
                  (^state7)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
REPEAT ( EVAL_TAC>>
FULL_SIMP_TAC list_ss [] )
);



(*** stmt seq  statement reduction --concrete values -- ***)

val prog7a =  ``((stmt_seq ^prog5 ^prog2))``;
val prog7b =  ``((stmt_seq stmt_empty (^prog2)))``;
val prog7c =  ``(^prog2)``;
val state7a = ``(state_tup (stacks_tup ^scopelist10 []) status_running): state``;
val state7b = ``(state_tup (stacks_tup ^scopelist13 []) status_running): state``;
val state7c = ``(state_tup (stacks_tup ^scopelist14 []) status_running): state``;

val test_stmt_seq1 =
prove(`` stmt_red (^prog7a) 
                  (^state7a)
                  (^prog7b) 
                  (^state7b)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);


val test_stmt_seq2 =
prove(`` stmt_red (^prog7b) 
                  (^state7b)
                  (^prog7c) 
                  (^state7b)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>

EVAL_TAC>>
FULL_SIMP_TAC list_ss []     (*unresolved subgoal TODO:Check with didrik*)



);


(*** verify  statement reduction --concrete values -- ***)


val prog8a =  ``stmt_verify (^cond1) (e_v (v_err "PacketTooShort"))``;
val prog8b =  ``stmt_verify (e_v (v_bool  T )) (e_v (v_err "PacketTooShort"))``;
val prog8c =  ``stmt_verify (^cond2) (e_v (v_err "PacketTooShort"))``;
val prog8d =  ``stmt_verify (e_v (v_bool  F )) (e_v (v_err "PacketTooShort"))``;
val prog8e =  ``stmt_empty``;
val prog8f =  ````;
val state8a = ``(state_tup (stacks_tup ^scopelist10 []) status_running): state``;

val test_stmt_verify1 =
prove(`` stmt_red (^prog8a) 
                  (^state8a)
                  (^prog8b) 
                  (^state8a)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);


val test_stmt_verify2 =
prove(`` stmt_red (^prog8b) 
                  (^state8a)
                  (^prog8e) 
                  (^state8a)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);



val test_stmt_verify3 =
prove(`` stmt_red (^prog8c) 
                  (^state8a)
                  (^prog8d) 
                  (^state8a)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])
);



val test_stmt_verify4 =
prove(`` stmt_red (^prog8d) 
                  (^state8a)
                  (^prog8e) 
                  (^state8a)  ``,
REPEAT (RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss [])    (*ask Didkrik about declaring before assigning*)
);



(*** transitions stmt reduction --concrete values -- ***)
val prog9a =  ``stmt_trans (e_var "MoveNext") ``;
val prog9b =  ``stmt_empty``;
val prog9c =  ``stmt_trans (e_var "accept") ``;
val prog9d =  ``stmt_trans (e_var "reject") ``;

val state9a = ``(state_tup (stacks_tup ^scopelist10 []) status_running): state``;
val state9b = ``(state_tup (stacks_tup ^scopelist10 []) (status_pars_next (pars_next_trans "MoveNext"))): state``;
val state9c = ``(state_tup (stacks_tup ^scopelist10 []) (status_pars_next (pars_next_pars_fin pars_finaccept))): state``;
val state9d = ``(state_tup (stacks_tup ^scopelist10 []) (status_pars_next (pars_next_pars_fin pars_finreject))): state``;



val test_stmt_trans1 =
prove(`` stmt_red (^prog9a) 
                  (^state9a)
                  (^prog9b) 
                  (^state9b)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);


val test_stmt_trans2 =
prove(`` stmt_red (^prog9c) 
                  (^state9a)
                  (^prog9b) 
                  (^state9c)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);

val test_stmt_trans3 =
prove(`` stmt_red (^prog9d) 
                  (^state9a)
                  (^prog9b) 
                  (^state9d)  ``,
RW.ONCE_RW_TAC[e_red_cases] >>
EVAL_TAC>>
FULL_SIMP_TAC list_ss []
);
