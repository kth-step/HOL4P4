open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

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
open alistTheory;


open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory;
     
open bdd_genTheory;     
open pred_specTheory;     
open policy_specTheory;   
open tables_specTheory;
open bdd_isomorphTheory;
open bdd_end_to_endTheory;     

open policy_arith_to_varTheory;
open table_var_to_arithTheory;
open table_arith_to_intervalTheory;

open bdd_auxTheory;
open table_bs_propertiesTheory;
     


val _ = load "bdd_utils";   

val _ = new_theory "bdd_test_cases";


    
(* a few types abbreviations *)
val _ = type_abbrev("BDD_tbl_type", “:(( (string# num list) var_table_list, (string# num list) action_expr) BDD)”);

val _ = type_abbrev("struc_tbl_type", “:((( atom_var list # num # (string# num list) action_expr) list list # num,
                                          (string# num list) action_expr) decision_structure)”);

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

(*
val _ = type_abbrev("arith_rule_typ", “:((string# num list) action_expr) arith_rule”);
val _ = type_abbrev("arith_policy_typ", “:((string# num list) action_expr) arith_policy”);
*)





        
    
(****************************************************************)
(****************************************************************)
(*                            POLICY 1                          *)
(****************************************************************)
(****************************************************************)
   
(* 
      x ∧ y : fwd(1)
          z : fwd(2)
          T : drop() 
*)
        

(* policy 1: arith POLICY representation *)

val test_pd_type1 = “[("h" , type_record [("ttl", type_length 8);
                                          ("flag", type_length 4)])]”;

                                          
val is_high_ttl = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(BDDUtils.make_bv 100 8) )”;
val is_low_ttl = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(BDDUtils.make_bv 1 8) )”;
val is_flag_ok = “(arithm_le (lv_acc (lv_x "h") "flag") ^(BDDUtils.make_bv 3 4) )”;

        
val policy1_me1 =   “[("x", ^is_high_ttl);
                      ("y", ^is_low_ttl );
                      ("z", ^is_flag_ok)]”;

val policy1_full_order = “[("a",["x";"y"]);("b",["z"])]”;                      

val policy1_order = “["x";"y";"z"]”;                      

    
val arith_policy1_rule1 = “(arith_and (arith_a ^is_high_ttl) ( arith_a ^is_low_ttl) ,
                            action ("fwd",[(1:num)])):((string# num list) action_expr) arith_rule”;
                            
val arith_policy1_rule2 = “(arith_a (^is_flag_ok) , action ("fwd",[2]))
                           :((string# num list) action_expr) arith_rule”;
                           
val arith_policy1_rule3 = “(arith_a a_True, action ("drop",[])):((string# num list) action_expr) arith_rule”;
                    

val arith_policy1 =   “[^arith_policy1_rule1 ;
                        ^arith_policy1_rule2 ;
                        ^arith_policy1_rule3]:((string# num list) action_expr) arith_policy”;


                        
val arith_policy1_eval = EVAL “convert_arith_to_var_policy ^arith_policy1 ^policy1_me1”;


val var_policy1 = optionSyntax.dest_some (rhs (concl arith_policy1_eval));

(* first establish distinction *)
val policy1_me1_fst_distinct = EVAL ``ALL_DISTINCT (MAP FST ^policy1_me1)``;
val policy1_me1_snd_distinct = EVAL ``ALL_DISTINCT (MAP SND ^policy1_me1)``;


val all_distinct_conj = CONJ policy1_me1_fst_distinct policy1_me1_snd_distinct;



val alookup_cond_thm = EVAL “∀var atom. ALOOKUP ^policy1_me1 var = SOME atom ⇒
                                        ALOOKUP m_v var = eval_arithm_atom packet_input atom”;


val arith_policy1_var_policy1_thm = REWRITE_RULE[all_distinct_conj, arith_policy1_eval]
(ISPECL[arith_policy1, var_policy1, policy1_me1] policy_airth_to_var_sem_conversion_correct);  



        
(* policy 1: var POLICY representation *)
(*   
val var_policy1_rule1 = ``(And (Var "x") (Var "y"), action ("fwd",[1])): action_rule_type``;
val var_policy1_rule2 = ``(Var "z", action ("fwd",[2])): action_rule_type``;
val var_policy1_rule3 = ``(True, action ("drop",[])): action_rule_type``;


val var_policy1 = ``[^var_policy1_rule1; ^var_policy1_rule2; ^var_policy1_rule3 ] : action_policy_type``;
*)

val eval_policy1_full_opt = EVAL ``mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ["x";"y";"z"] 1``;
val eval_policy1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy1_full_opt));


(* automatically generate a table*)
val test_groupings1 = rhs(concl(EVAL policy1_full_order));
val test_action_table1_auto = BDDUtils.bdd_to_tables_iterative eval_policy1_full_opt_rhs test_groupings1;

(* now create a BDD for the table*)    
val eval_table1_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^test_action_table1_auto))]) [] ["x";"y";"z"] 1”;
val eval_table1_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table1_full_opt_auto));

(* get I, and check if isisIsomorph *)
val get_i_policy1 = BDDUtils.pairBDDs (eval_table1_full_opt_auto_rhs , eval_table1_full_opt_auto_rhs);
val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy1 ^eval_table1_full_opt_auto_rhs ^eval_table1_full_opt_auto_rhs”;

(* get a theorem out*)
val policy1_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^test_action_table1_auto ["x";"y";"z"] ^get_i_policy1 ”;     
val policy1_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy1_thm_init;    


(* from var tables to final single interval table*)


val only_var_table1 = fst (dest_pair test_action_table1_auto);
   
                   

val convert_to_interval1 = EVAL “convert_var_to_sinterval_tables ^only_var_table1 ^policy1_me1  ^test_pd_type1”;   


val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval1));



     
val convert_var_to_sinterval_tables1_thm =
REWRITE_RULE [] (ISPECL[only_var_table1, only_interval_table1, “0:num”, policy1_me1, test_pd_type1 ] correct_tables_from_var_to_sinterval_thm);        



val final_table1_thm = SIMP_RULE bool_ss [convert_to_interval1] convert_var_to_sinterval_tables1_thm;    






Definition mv_from_me_and_packet_def:
  mv_from_me_and_packet me packet_input =
  MAP (\(x,arith_atom). 
        case eval_arithm_atom packet_input arith_atom of
          NONE => NONE
        | SOME v => SOME (x, v)
      ) me
End

Definition create_mv_def:
  create_mv me packet_input =
  let all = mv_from_me_and_packet me packet_input in
    let filtered = FILTER IS_SOME all in
      MAP THE filtered
End
                                     
 


Definition every_lval_in_me_in_type_def:
  every_lval_in_me_in_type pd_type me =
   EVERY (\(x,atom).  case (get_lval_from_arith atom) of
                      | is_lval lval => (case resolve_lval_type pd_type lval of
                                         | SOME (type_length n) => T
                                         | _ => F ) 
                      | _ => T) me                      
End



Definition ops_in_me_length_format_def:
  ops_in_me_length_format pd_type me =
  EVERY (\(x,atom).  case atom of
                     | a_True => T
                     | a_False => F           
                     | arithm_ge lval m => (case resolve_lval_type pd_type lval of
                                            | SOME (type_length n) => (n = SND m) 
                                            | _ => F )
                     | arithm_le lval m => (case resolve_lval_type pd_type lval of
                                            | SOME (type_length n) => (n = SND m) 
                                            | _ => F ) 
        ) me                      
End
     

     
    
Theorem lval_in_me_distinct_imp_cond1:
∀ me pd_type packet_input .
  ALL_DISTINCT (MAP FST me) ∧
  every_lval_in_me_in_type pd_type me ⇒
  (∀var atom.
     ALOOKUP me var = SOME atom ⇒
     ALOOKUP (create_mv me packet_input) var = eval_arithm_atom packet_input atom)
Proof
Induct >>
rpt strip_tac >>
gvs[create_mv_def] >>                 
rw[mv_from_me_and_packet_def] >|[
    PairCases_on ‘h’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[every_lval_in_me_in_type_def] >>
    res_tac >>
    gvs[mv_from_me_and_packet_def]
    ,
    PairCases_on ‘h’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
        simp[ALOOKUP_NONE] >>
        gvs[MEM_MAP] >>
        rpt strip_tac >>
        gvs[MEM_FILTER] >>
        gvs[MEM_MAP] >>
        PairCases_on ‘y’ >> gvs[] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
                           
        ,
        gvs[every_lval_in_me_in_type_def] >>
        res_tac >>
        gvs[mv_from_me_and_packet_def]    
      ]
  ]
QED
         
                             
val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type1 ^policy1_me1”;
val all_distinct_fst_me_thm = EVAL “ALL_DISTINCT (MAP FST ^policy1_me1)”;

val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, all_distinct_fst_me_thm] (ISPECL[policy1_me1, test_pd_type1 ] lval_in_me_distinct_imp_cond1);   



  
Definition mv_dom_vars_exec_def:
  mv_dom_vars_exec mv vars =
  EVERY (\x. ALOOKUP mv x ≠ NONE) vars
End

Theorem lookup_is_some_not_none_eq:
  ∀ mv x.
    lookup_is_some mv x ⇔ ALOOKUP mv x ≠ NONE
Proof
  Induct >>
  gvs[lookup_is_some_def] >>
  rpt strip_tac >>
  EQ_TAC >>
  rpt strip_tac >>
  gvs[] >>
  Cases_on ‘ALOOKUP (h::mv) x’ >> gvs[]
QED                  
                                 
        
Theorem mv_dom_vars_exec_eq:
  ∀ mv vars.
    mv_dom_vars mv vars = mv_dom_vars_exec mv vars
Proof
  rw[mv_dom_vars_def, mv_dom_vars_exec_def] >>
  gvs[EVERY_MEM, lookup_is_some_not_none_eq]
QED



Definition in_order_then_in_me_def:
  in_order_then_in_me order me =
  EVERY (\x. ALOOKUP me x ≠ NONE) order
End



Theorem wf_format_imp_cond2:
  ∀ me pd_type order.
    ∀ packet_input.
      in_order_then_in_me order me ∧
      ops_in_me_length_format pd_type me ∧
      wf_packet pd_type packet_input ∧
      ALL_DISTINCT (MAP FST me) ∧
      every_lval_in_me_in_type pd_type me ⇒
      mv_dom_vars (create_mv me packet_input) order
Proof
  rw[in_order_then_in_me_def] >>
  gvs[mv_dom_vars_exec_eq] >>
  gvs[mv_dom_vars_exec_def] >>
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  res_tac >>
  
  
  Cases_on ‘ALOOKUP me x’ >> gvs[] >>
  imp_res_tac MEM_ALOOKUP_DISTINCT >>
  
  gvs[every_lval_in_me_in_type_def] >>
  gvs[EVERY_MEM] >>
  
  res_tac >>
  gvs[create_mv_def] >>
  gvs[mv_from_me_and_packet_def] >>         
  gvs[ALOOKUP_NONE] >>
  gvs[MEM_MAP] >>
  gvs[MEM_FILTER] >>
  gvs[MEM_MAP] >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(x,THE (eval_arithm_atom packet_input x'))’])) >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘SOME (x,THE (eval_arithm_atom packet_input x'))’])) >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(x,x')’])) >> gvs[] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  Cases_on ‘x'’ >> 
  gvs[eval_arithm_atom_def] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  (* le and ge same proof *)
  (
  (* first and third subgoals *)
  res_tac >>
  fs[get_lval_from_arith_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[wf_packet_def] >>
  res_tac >> gvs[] >>
  
  (* reach here only for second subgoal *)
  
  PairCases_on ‘bs’ >>
  PairCases_on ‘y’ >>
  PairCases_on ‘y'’ >>
  gvs[] >>
  
  imp_res_tac MEM_ALOOKUP_DISTINCT >>
  gvs[] >>
  
  gvs[ops_in_me_length_format_def] >>
  gvs[EVERY_MEM] >>
  res_tac >>
  fs[] >>
  
  gvs[] >>
  
  PairCases_on ‘p’ >> gvs[] >>
  imp_res_tac last_edge_of_binpred_neg >> gvs[]
  )
QED








              
val in_order_then_in_me_thm = EVAL “in_order_then_in_me ^policy1_order ^policy1_me1”;
val ops_in_me_length_format_thm = EVAL “ops_in_me_length_format ^test_pd_type1 ^policy1_me1”;

val cond2_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, all_distinct_fst_me_thm,
                             in_order_then_in_me_thm, ops_in_me_length_format_thm]
                             (ISPECL[policy1_me1, test_pd_type1, policy1_order ]
                                    wf_format_imp_cond2);   


                                        




Theorem create_mv_all_distinct:
  ∀ me packet_input.
    ALL_DISTINCT (MAP FST me) ⇒ ALL_DISTINCT (MAP FST (create_mv me packet_input))
Proof
  Induct >>
  gvs[create_mv_def] >>
  gvs[mv_from_me_and_packet_def] >>   
  rpt strip_tac >>
  
  PairCases_on ‘h’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >>
  Cases_on ‘y'’ >> gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘y’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED
                                              

                                        
Theorem create_mv_normalization:
  ∀ h me packet_input.
  create_mv (h::me) packet_input = (create_mv [h] packet_input)++(create_mv me packet_input)
Proof
  rw[create_mv_def] >>
  gvs[mv_from_me_and_packet_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Theorem ops_in_me_length_format_normalization:
  ∀ h me pd_type.
    ops_in_me_length_format pd_type (h::me) = (ops_in_me_length_format pd_type [h] ∧
                                               ops_in_me_length_format pd_type me)
Proof
  rw[ops_in_me_length_format_def]
QED


        
Theorem every_lval_in_me_in_type_normalization:
  ∀ h me pd_type.
    every_lval_in_me_in_type pd_type (h::me) = (every_lval_in_me_in_type pd_type [h] ∧
                                                every_lval_in_me_in_type pd_type me )
Proof
  rw[every_lval_in_me_in_type_def]
QED

        
                               
Theorem if_in_create_mv_then_in_me:                                  
  ∀ me var y.
    ∀ packet_input.
      ALL_DISTINCT (MAP FST me) ∧
      ALOOKUP (create_mv me packet_input) var = SOME y ⇒
      ∃y'. ALOOKUP me var = SOME y'
Proof
  Induct >>
  rw[] >-
   gvs[create_mv_def, mv_from_me_and_packet_def] >>
  
  imp_res_tac create_mv_all_distinct >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’])) >> 
  
  gvs[Once create_mv_normalization] >>
  gvs[ALOOKUP_APPEND] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    res_tac >>
    PairCases_on ‘h’ >> gvs[] >>
    BasicProvers.FULL_CASE_TAC >> gvs[]
    ,
    PairCases_on ‘h’ >> gvs[] >>
    BasicProvers.FULL_CASE_TAC >> gvs[] >>
    gvs[create_mv_def, mv_from_me_and_packet_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
  ]
QED



        
Theorem wf_format_and_fail_create_single:
  ∀ pd_type h var.
    ∀ packet_input.
      ops_in_me_length_format pd_type [h] ∧
      wf_packet pd_type packet_input ∧
      every_lval_in_me_in_type pd_type [h]  ∧
      wf_packet pd_type packet_input ∧
      ALOOKUP (create_mv [h] packet_input) var = NONE ⇒
      FST h ≠ var
Proof
  
  rw[create_mv_def] >>
  gvs[mv_from_me_and_packet_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[every_lval_in_me_in_type_def] >>
  
  
  Cases_on ‘h1’ >>
  gvs[eval_arithm_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  
  gvs[get_lval_from_arith_def] >>
  
  gvs[wf_packet_def] >>      
  res_tac >>
  gvs[] >>
  
  gvs[ops_in_me_length_format_def] >>
  PairCases_on ‘p’ >> gvs[] >>
  PairCases_on ‘bs’ >> gvs[] >>
  imp_res_tac last_edge_of_binpred_neg >> gvs[]
QED





Theorem if_in_me_then_in_create_mv:                                  
  ∀ me pd_type var y.
    ∀ packet_input.
      ops_in_me_length_format pd_type me ∧
      wf_packet pd_type packet_input ∧
      ALL_DISTINCT (MAP FST me) ∧
      every_lval_in_me_in_type pd_type me ∧
      ALOOKUP me var = SOME y
      ⇒
      ∃y'. ALOOKUP (create_mv me packet_input) var = SOME y'
Proof

  Induct >-
   rw[] >>
  rpt strip_tac >>
  
  imp_res_tac create_mv_all_distinct >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’])) >> 
  
  gvs[Once create_mv_normalization] >>
  simp[Once create_mv_normalization] >>
  
  gvs[ALOOKUP_APPEND] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  rgs[Once ops_in_me_length_format_normalization] >>
  rgs[Once every_lval_in_me_in_type_normalization] >>
  
  res_tac >>
  
  imp_res_tac wf_format_and_fail_create_single >>
  PairCases_on ‘h’ >> gvs[] >>
  res_tac >> gvs[]
QED
              



Theorem wf_format_imp_cond3:                                        
  ∀ me pd_type.
    ∀ packet_input.
      ops_in_me_length_format pd_type me ∧
      wf_packet pd_type packet_input ∧
      ALL_DISTINCT (MAP FST me) ∧
      every_lval_in_me_in_type pd_type me ⇒
      (∀var. lookup_is_some (create_mv me packet_input) var ⇔
               lookup_is_some me var)
Proof
  rw[lookup_is_some_def] >>
  EQ_TAC >> strip_tac >|[
    imp_res_tac if_in_create_mv_then_in_me >> gvs[]
    ,
    imp_res_tac if_in_me_then_in_create_mv >> gvs[]
  ]
QED


   

val cond3_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, all_distinct_fst_me_thm,
                             in_order_then_in_me_thm, ops_in_me_length_format_thm]
                             (ISPECL[policy1_me1, test_pd_type1]
                                    wf_format_imp_cond3);   





    
val final_thm = prove(
“! packet_input .
 wf_packet ^test_pd_type1 packet_input ⇒ 
 sem_arith_policy ^arith_policy1 packet_input = 
 sem_sinterval_tables (^only_interval_table1,0) packet_input”
,

rpt strip_tac >>
assume_tac arith_policy1_var_policy1_thm >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy1_me1 packet_input)’])) >>

gvs[cond1_thm] >>

assume_tac policy1_thm >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘(create_mv ^policy1_me1 packet_input)’])) >>

imp_res_tac cond2_thm >>
gvs[] >>
          
assume_tac final_table1_thm >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy1_me1 packet_input)’])) >>
gvs[cond1_thm] >>

gvs[cond3_thm]
);

















             
    
(*
                                
(****************************************************************)
(****************************************************************)
(*                            POLICY 2                          *)
(****************************************************************)
(****************************************************************)
   
(*    This is the camus paper example
          x     : fwd(1)
          x ∧ z : fwd(2)
          y ∧ w : fwd(3)  
          T     : drop()
*)


                                                        
(* policy 2: var policy representation *)
val var_policy2_rule1 = ``(Var "x", action ("fwd",[1])): action_rule_type``;
val var_policy2_rule2 = ``(And (Var "x") (Var "z"), action ("fwd",[2])): action_rule_type``;
val var_policy2_rule3 = ``(And (Var "y") (Var "w"), action ("fwd",[3])): action_rule_type``;
val var_policy2_rule4 = ``(True, action ("drop",[])): action_rule_type``;

val var_policy2 = ``[ ^var_policy2_rule1; ^var_policy2_rule2; ^var_policy2_rule3; ^var_policy2_rule4 ] : action_policy_type``;

val eval_policy2_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy2))]) [] ["x";"y";"z";"w"] 1”;
val eval_policy2_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy2_full_opt));



(* automatically generate a table*)
val test_groupings2 = rhs(concl(EVAL “[("a",["x";"y"]);("b",["z";"w"])]”));
val test_action_table2_auto =BDDUtils.bdd_to_tables_iterative eval_policy2_full_opt_rhs test_groupings2;

(* now create a BDD for the table*)    
val eval_table2_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^test_action_table2_auto))]) [] ["x";"y";"z";"w"] 1”;
val eval_table2_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table2_full_opt_auto));

(* get I, and check if isisIsomorph *)
val get_i_policy2 = BDDUtils.pairBDDs (eval_table2_full_opt_auto_rhs , eval_table2_full_opt_auto_rhs);
val is_tbl_policy2_iso = EVAL “isIsomorph_exec ^get_i_policy2 ^eval_table2_full_opt_auto_rhs ^eval_table2_full_opt_auto_rhs”;

(* get a theorem out*)
val policy2_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy2 ^test_action_table2_auto ["x";"y";"z";"w"] ^get_i_policy2 ”;     
val policy2_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy2_thm_init;     


*)



    
(*  (* Manual effort*)
(* policy 2: var table representation *)
val var_tbl1_line1 = ``([(Var "x")]                     , 0, state 1): (string# num list) line``;
val var_tbl1_line2 = ``([Not (Var "x"); (Var "y")]      , 0, state 3): (string# num list) line``;
val var_tbl1_line3 = ``([Not (Var "x"); Not (Var "y")]  , 0, state 4): (string# num list) line``;

val var_tbl1 = ``[^var_tbl1_line1; ^var_tbl1_line2; ^var_tbl1_line3] : (string# num list) table``;
     

val var_tbl2_line1 = ``([(Var "z"); (Var "w")]     , 3, state 7): (string# num list) line``;
val var_tbl2_line2 = ``([(Var "z"); Not (Var "w")] , 3, state 8): (string# num list) line``;
val var_tbl2_line3 = ``([Not (Var "z"); (Var "w")] , 3, state 9): (string# num list) line``;
val var_tbl2_line4 = ``([Not (Var "z"); Not (Var "w")] , 3, state 10): (string# num list) line``;
val var_tbl2_line5 = ``([True]                         , 1, state 1): (string# num list) line``;
val var_tbl2_line6 = ``([True]                         , 4, state 4): (string# num list) line``;


val var_tbl2 = ``[^var_tbl2_line1; ^var_tbl2_line2; ^var_tbl2_line3;
                  ^var_tbl2_line4; ^var_tbl2_line5; ^var_tbl2_line6] : (string# num list) table``;


val var_tbl3_line1 = ``([True] , 1, action ("fwd",[1])): (string# num list) line``;
val var_tbl3_line2 = ``([True] , 4, action ("drop",[])): (string# num list) line``;
val var_tbl3_line3 = ``([True] , 7, action ("fwd",[3])): (string# num list) line``;
val var_tbl3_line4 = ``([True] , 8, action ("drop",[])): (string# num list) line``;
val var_tbl3_line5 = ``([True] , 9, action ("fwd",[3])): (string# num list) line``;
val var_tbl3_line6 = ``([True] , 10, action ("drop",[])): (string# num list) line``;

val var_tbl3 = ``[^var_tbl3_line1; ^var_tbl3_line2; ^var_tbl3_line3;
                 ^var_tbl3_line4; ^var_tbl3_line5; ^var_tbl3_line6] : (string# num list) table``;

val var_tbls2 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) var_table_list) ``;
val var_tbls2_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) var_table_list),(0:num)) ``;


val eval_table2_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^var_tbls2_start))]) [] ["x";"y";"z";"w"] 1”;
val eval_table1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_table2_full_opt));

val get_i_policy2 = BDDUtils.pairBDDs (eval_policy2_full_opt_rhs, eval_table1_full_opt_rhs);
val is_tbl_policy2_iso = EVAL “isIsomorph_exec ^get_i_policy2 ^eval_policy2_full_opt_rhs ^eval_table1_full_opt_rhs”;
*)





(***************************************************)

(*
val AND = ``λ(p1,a1) (p2,a2). (arith_and p1 p2, a2)``;
val OR  = ``λ(p1,a1) (p2,a2). (arith_or p1 p2, a1)``; 
val NOT = ``λ(p,a). (arith_not p, a)``;
*)

(*
val test_packet = “[
  ("h", val_record [
    ("ip", val_record [
      ("ttl", val_num 64);
      ("proto", val_num 6);
      ("version", val_num 4)
    ]);
    ("src_zone", val_num 1);
    ("threat_score", val_num 30);
    ("auth_status", val_num 1)
  ])
  ]”;

  
val is_tcp =      “arith_a (arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "proto") 6)”;
val is_high_ttl = “arith_a (arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "ttl") 60)”;
val is_internal = “arith_a (arithm_le (lv_acc (lv_x "h") "src_zone") 1)”;
val is_malicious = “arith_a (arithm_ge (lv_acc (lv_x "h") "threat_score") 80)”;


val policy3_me1 = “[
  ("is_tcp", (arithm_eq (lv_acc (lv_acc (lv_x "h") "ip") "proto") 6));
  ("is_high_ttl", (arithm_gt (lv_acc (lv_acc (lv_x "h") "ip") "ttl") 60));
  ("is_internal",  (arithm_eq (lv_acc (lv_x "h") "src_zone") 1));
  ("is_malicious",  (arithm_gt (lv_acc (lv_x "h") "threat_score") 80))
]”;

val arith_policy3_rule1 = “(arith_and ^is_tcp ^is_high_ttl , action ("fwd",[(1:num)])):((string# num list) action_expr) arith_rule”;
val arith_policy3_rule2 = “(arith_or (arith_not ^is_tcp) (^is_high_ttl), action ("fwd",[2])) :((string# num list) action_expr) arith_rule”;
val arith_policy3_rule3 = “(arith_a a_True, action ("drop",[])):((string# num list) action_expr) arith_rule”;
                    

val arith_policy3 =   “[ ^arith_policy3_rule1 ;
                        ^arith_policy3_rule2 ;
                        ^arith_policy3_rule3]:((string# num list) action_expr) arith_policy”;


val arith_policy3_eval = EVAL convert_arith_to_var_policy ^arith_policy3 ^policy3_me1”;

val var_policy3 = optionSyntax.dest_some (rhs (concl arith_policy3_eval));


(* first establish distinction *)
val policy3_me1_fst_distinct = EVAL ``ALL_DISTINCT (MAP FST ^policy3_me1)``;
val policy3_me1_snd_distinct = EVAL ``ALL_DISTINCT (MAP SND ^policy3_me1)``;

(*second, combine them  *)
val all_distinct_conj = CONJ policy3_me1_fst_distinct policy3_me1_snd_distinct;

val alookup_cond_thm = EVAL “∀var atom. ALOOKUP ^policy3_me1 var = SOME atom ⇒ ALOOKUP m_v var = eval_arithm_atom packet_input atom”;

                
val arith_policy3_var_policy3_thm = REWRITE_RULE[all_distinct_conj, arith_policy3_eval]
(ISPECL[arith_policy3, var_policy3, policy3_me1] policy_airth_to_var_sem_conversion_correct);        

*)

                      
val _ = export_theory ();







