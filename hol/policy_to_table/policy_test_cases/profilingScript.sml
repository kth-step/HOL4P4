open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;
open bdd_genTheory;
open bdd_gen_newTheory;
open numeralTheory;
open alistTheory;


open pred_specTheory;


open bdd_genTheory;
open policy_arith_to_varTheory;

open bdd_utilsLib;
open fwd_proofLib;   


val _ = new_theory "profiling";

(*

        fun take_first_three tuple_term =
    let val (a, bc_d) = pairSyntax.dest_pair tuple_term
        val (b, c_d) = pairSyntax.dest_pair bc_d
        val (c, _) = pairSyntax.dest_pair c_d
    in pairSyntax.mk_pair (a, pairSyntax.mk_pair (b, c)) end;

                          

fun take_fourth tuple_term =
    let val (a, bc_d) = pairSyntax.dest_pair tuple_term
        val (b, c_d) = pairSyntax.dest_pair bc_d
        val (c, d) = pairSyntax.dest_pair c_d
    in d end;


         
fun bdd_mini_components thm =
    let val tuple_term = optionSyntax.dest_some (rhs (concl thm))
    in take_first_three tuple_term end;

fun bdd_content_components thm =
    let val tuple_term = optionSyntax.dest_some (rhs (concl thm))
    in take_fourth tuple_term end;


    
fun add_fourth_component triple_term fourth_component =
    let val (a, b_c) = pairSyntax.dest_pair triple_term
        val (b, c) = pairSyntax.dest_pair b_c
    in
        pairSyntax.mk_pair (a, 
            pairSyntax.mk_pair (b, 
                pairSyntax.mk_pair (c, fourth_component)))
    end;


val eval_table_full_layer1 = time EVAL
      “mk_BDDPred_new pred_structure (0n,[],[(0n, id_non_termn (NONE), 0n)], [(0n, Var "x")]) [] ["x"] 1n”;
val eval_table_full_layer1_rhs = bdd_mini_components eval_table_full_layer1;
val eval_table_full_layer1_rhs_fourth = bdd_content_components eval_table_full_layer1;

val eval_table_full_opt_layer1 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer1_rhs ^policy_order”;
val eval_table_full_opt_layer1_rhs = add_fourth_component (rhs (concl eval_table_full_opt_layer1)) eval_table_full_layer1_rhs_fourth;



val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));
    



val eval_policy_full_opt = EVAL “mk_BDDPred_opt_new policy_structure (0n,[],[(0n, id_non_termn NONE, 0n)], [0n, ^var_policy]) [] ^policy_order 1n”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));
    
mk_BDDPred_opt_new_def


    
  *)  



         
    
fun mk_BDDPred_opt_new_sml rec_flag bdd_sep l xs c =
    case xs of
        [] => SOME bdd_sep
      | x::xs' =>
          let
                val time1_cpu = Timer.startCPUTimer ();
               val time1_real = Timer.startRealTimer ();
               val result_thm =  EVAL “body_of_mk_new ^rec_flag ^bdd_sep ^x ^c”
               val _ = time_stage ("body_of_mk_new  ", time1_cpu, time1_real);

                                        
                val result_term = rhs (concl result_thm)
            in
                if optionSyntax.is_none result_term then
                    NONE
                else
                    let
                        (* Extract the components step by step with debugging *)
                        val the_content = optionSyntax.dest_some result_term
                        val (bdd_quad, c') = pairSyntax.dest_pair the_content
                        
                        (* bdd_quad should be: (r, edges, labels_id, labels_content) *)
                        val (r, rest1) = pairSyntax.dest_pair bdd_quad
                        val (edges, rest2) = pairSyntax.dest_pair rest1  
                        val (labels_id, labels_content) = pairSyntax.dest_pair rest2
                        
                        val optimize_input = pairSyntax.mk_pair(r, 
                                            pairSyntax.mk_pair(edges, labels_id))
                        
                        val var_list_term = listSyntax.mk_list(x::l, ``:string``)


                       val time2_cpu = Timer.startCPUTimer ();
                       val time2_real = Timer.startRealTimer ();
                                             
                        val optimized_thm =  EVAL “optimize_bdd_new ^optimize_input ^var_list_term”
                        val optimized_result = rhs (concl optimized_thm )
                       val _ = time_stage ("optimize  ", time2_cpu, time2_real);

                        (*val _ = print ("Optimized result: " ^ term_to_string optimized_result ^ "\n") *)
                        
                        (* Extract from the optimized triple *)
                        val (r', opt_rest1) = pairSyntax.dest_pair optimized_result
                        val (edges', labels_id') = pairSyntax.dest_pair opt_rest1
                        
                        (* Build new quadruple *)
                        val new_bdd_sep = pairSyntax.mk_pair(r',
                                        pairSyntax.mk_pair(edges',
                                        pairSyntax.mk_pair(labels_id', labels_content)))
                    in
                        mk_BDDPred_opt_new_sml rec_flag new_bdd_sep (x::l) xs' c'
                    end
            end

(*
val result = mk_BDDPred_opt_new_sml “pred_structure”
                               “(0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")])”
                               [] [“"x"”, “"y"”] “1n”



EVAL “mk_BDDPred_opt_new pred_structure (0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")]) [] ["x"; "y"] 1n”
*)



fun mk_BDDPred_opt_new_thm rec_flag bdd_sep xs =
    let
        val result = mk_BDDPred_opt_new_sml rec_flag bdd_sep [] xs “1n”
        val l_term = listSyntax.mk_list([], ``:string``)
        val xs_term = listSyntax.mk_list(xs, ``:string``)
    in
        case result of
            NONE => mk_thm([], ``mk_BDDPred_opt_new ^rec_flag ^bdd_sep ^l_term ^xs_term 1n = NONE``)
          | SOME res => mk_thm([], ``mk_BDDPred_opt_new ^rec_flag ^bdd_sep ^l_term ^xs_term 1n = SOME ^res``)
    end;



(*
val a = mk_BDDPred_opt_new_thm “pred_structure”
                               “(0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")])”
                               [“"x"”, “"y"”] 
*)

val rec_flag = ``policy_structure : ((pred # (string # num list) action_expr) list, (string # num list) action_expr) decision_structure``
val rec_flag_table = ``table_structure : ((( atom_var list # num # (string# num list) action_expr) list list # num,
                                          (string# num list) action_expr) decision_structure)``        
  





  
val policy_order_list = listSyntax.dest_list policy_order |> #1


(*convert arith policy to var policy*)

val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));



(***********************************************)
    
(* eval policy, OLD BDD*)
    
val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));
    
(* eval policy, new BDD*)

val new_eval_policy_full_opt = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, id_non_termn (NONE), 0)], [(0,^var_policy)]) [] ^policy_order 1”;
    
(* sml procedure policy, new BDD*)

val new_procedure_full_opt = mk_BDDPred_opt_new_thm rec_flag “(0n,[]:edges,[(0n, (id_non_termn NONE):(string # num list) action_expr id, 0n)], [(0n,^var_policy)])” policy_order_list 
   

    
(**** generate a var table *****)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative old_eval_policy_full_opt_rhs test_groupings;


(* eval TABLE, OLD BDD*)

val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));
    
(* eval TABLE, new BDD*)

val new_eval_table_full_opt = EVAL “mk_BDDPred_opt_new table_structure (0,[],[(0, id_non_termn (NONE), 0)], [(0,^gen_var_table_auto)]) [] ^policy_order 1”;
    
(* sml procedure TABLE, new BDD*)

val new_procedure_table_full_opt = mk_BDDPred_opt_new_thm rec_flag_table “(0n,[]:edges,[(0n, (id_non_termn NONE):(string # num list) action_expr id, 0n)], [(0n,^gen_var_table_auto)])” policy_order_list 
   






    



val _ = export_theory ();


(*
                               
(* Theorem for body_of_mk_new with first variable *)
val body_thm1 = 
    EVAL ``body_of_mk_new pred_structure
             (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) "x" 1``;

(* Theorem for optimize_bdd_new on first step *)
val optimize_thm1 =
    EVAL ``optimize_bdd_new (0,[(0,1,2)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
          (2,id_termn F,1)]) ["x"]``;

(* Theorem for body_of_mk_new with second variable *)
val body_thm2 =
    EVAL ``body_of_mk_new pred_structure
             (0,[(0,1,2)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
          (2,id_termn F,1)],[(0,Var "y"); (1,False)]) "y" 3``;

(* Theorem for optimize_bdd_new on second step *)
val optimize_thm2 =
    EVAL ``optimize_bdd_new (0,[(0,1,2); (1,3,4)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn (SOME "y"),0);
          (2,id_termn F,1); (3,id_termn T,0); (4,id_termn F,1)]) ["y"; "x"]``;


(* Now prove the final theorem with all the reductions *)

val final_thm =
    SIMP_CONV (bool_ss) 
      [Once mk_BDDPred_opt_new_def, 
       body_thm1, optimize_thm1, body_thm2, optimize_thm2,
       optionTheory.option_case_def,    (* The actual option case theorem *)
       pairTheory.pair_case_thm]        (* The actual pair case theorem *)
      ``mk_BDDPred_opt_new pred_structure
          (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) []
          ["x"; "y"] 1``;

val final_thm_clean =
    SIMP_RULE (bool_ss) [LET_THM, FST, SND] final_thm;

    
val triple_reduction = prove(
  ``(λ(r',edges',labels_id'). f r' edges' labels_id') (a,b,c) = f a b c``,
  rw []);

val final_thm_beta =
    SIMP_RULE std_ss [triple_reduction] final_thm_clean;



----------------------------------------------------
val reduced = 
    REWRITE_CONV [Once mk_BDDPred_opt_new_def, body_thm1] 
      ``mk_BDDPred_opt_new pred_structure
          (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) []
          ["x"; "y"] 1``;

(* Now manually substitute the known values *)
val manual_thm = prove(
  ``(case SOME ((0,[(0,1,2)],
                [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
                 (2,id_termn F,1)],[(0,Var "y"); (1,False)]),3) of
      NONE => NONE
    | SOME ((r,edges,labels_id,labels_content),c') =>
        (let (r',edges',labels_id') = optimize_bdd_new (r,edges,labels_id) ["x"] in
         mk_BDDPred_opt_new pred_structure (r',edges',labels_id',labels_content) ["x"] ["y"] c')) =
    mk_BDDPred_opt_new pred_structure
      (0,[(0,1,2)],
       [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
        (2,id_termn F,1)],[(0,Var "y"); (1,False)]) ["x"] ["y"] 3``,
  rw [optimize_thm1]);

val final_thm_step1 = TRANS reduced manual_thm;

(* Continue with the recursive call *)
val final_thm_step2 = 
    REWRITE_RULE [Once mk_BDDPred_opt_new_def, body_thm2, optimize_thm2, mk_BDDPred_opt_new_def] 
                 final_thm_step1;


val case_reduction = prove(
  ``(case SOME x of NONE => a | SOME y => b y) = b x``,
  rw []);

val final_thm_step3 = SIMP_RULE std_ss [case_reduction] final_thm_step2;

(* Now we should have the final result *)
val final_thm = final_thm_step3;


val final_thm =
    REWRITE_RULE 
      [case_reduction,
       pairTheory.pair_case_def,
       BETA_THM,
       optimize_thm2] 
      final_thm_step2;

*)


fun mk_BDDPred_opt_new_sml2 rec_flag bdd l xs c =
    case xs of
        [] => SOME bdd
      | x::xs' =>
          let
                val time1_cpu = Timer.startCPUTimer ();
               val time1_real = Timer.startRealTimer ();
               val result_thm =  EVAL “body_of_mk ^rec_flag ^bdd ^x ^c”
               val _ = time_stage ("body_of_mk_new  ", time1_cpu, time1_real);

                                        
                val result_term = rhs (concl result_thm)
            in
                if optionSyntax.is_none result_term then
                    NONE
                else
                    let
                        (* Extract the components step by step with debugging *)
                        val the_content = optionSyntax.dest_some result_term
                        val (bdd_quad, c') = pairSyntax.dest_pair the_content
                        
                        val var_list_term = listSyntax.mk_list(x::l, ``:string``)


                       val time2_cpu = Timer.startCPUTimer ();
                       val time2_real = Timer.startRealTimer ();
                                             
                        val optimized_thm =  EVAL “optimize_bdd ^bdd_quad ^var_list_term”
                        val optimized_result = rhs (concl optimized_thm )
                       val _ = time_stage ("optimize  ", time2_cpu, time2_real);

                    in
                        mk_BDDPred_opt_new_sml2 rec_flag optimized_result (x::l) xs' c'
                    end
            end






fun mk_BDDPred_opt_new_thm2 rec_flag bdd xs =
    let
        val result = mk_BDDPred_opt_new_sml2 rec_flag bdd [] xs “1n”
        val l_term = listSyntax.mk_list([], ``:string``)
        val xs_term = listSyntax.mk_list(xs, ``:string``)
    in
        case result of
            NONE => mk_thm([], ``mk_BDDPred_opt ^rec_flag ^bdd ^l_term ^xs_term 1n = NONE``)
          | SOME res => mk_thm([], ``mk_BDDPred_opt ^rec_flag ^bdd ^l_term ^xs_term 1n = SOME ^res``)
    end;


--------------------------------------------------------------




  
val policy_order_list = listSyntax.dest_list policy_order |> #1


(*convert arith policy to var policy*)

val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


val new_procedure_full_opt2 = 
  mk_BDDPred_opt_new_thm2 rec_flag 
    “(0n, []:edges, [(0n, non_termn (NONE :string option, ^var_policy) :((pred # (string # num list) action_expr) list, (string # num list) action_expr) label)])” 
    policy_order_list
    



val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));
    


    
(**** generate a var table *****)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;



val _ = type_abbrev("tbl_type", “:((atom_var list # num # (string# num list) action_expr) list list)”);

val new_procedure_full_opt3 = 
  mk_BDDPred_opt_new_thm2 rec_flag_table 
    “(0n, []:edges, [
      (0n, 
        (non_termn : string option # ((atom_var list # num # (string # num list) action_expr) list list # num) -> 
                    ((atom_var list # num # (string # num list) action_expr) list list # num, 
                     (string # num list) action_expr) label)
          (NONE :string option, ^gen_var_table_auto)
      )
    ])” 
    policy_order_list





val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 4 3))”;
val is_small_packet = “(arithm_le (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 500 16))”;
val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(bdd_utilsLib.make_bv 200 8))”;
val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 8 4))”;

val policy_me =   “[("x", ^is_high_priority);
                    ("y", ^is_medium_priority);
                    ("z", ^is_small_packet);
                    ("w", ^is_young_packet);
                    ("q", ^is_control_type);
                    ("r", ^is_data_type)]”;

val policy_full_order = “[("a",["x";"y"]);
                          ("b",["z"]);
                          ("c",["w"]);
                          ("d",["q";"r"])]”;

val policy_order = “["x";"y";"z";"w";"q";"r"]”;

(* Rule 1: High priority small control packets - expedited forwarding *)
val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_small_packet) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

(* Rule 2: High priority data packets *)
val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_data_type),
                           action ("fwd",[1])):single_rule”;

(* Rule 3: Medium priority young packets *)
val arith_policy_rule3 = “(arith_and (arith_a ^is_medium_priority) (arith_a ^is_young_packet),
                           action ("fwd",[2])):single_rule”;

(* Rule 7: Default forward rule *)
val arith_policy_rule7 = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule7]:single_rule list”;


                       
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure2 (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));

    (*
EVAL “optimize_bdd (FST (THE (body_of_mk policy_structure ^old_eval_policy_full_opt_rhs "w" 12n))) ^policy_order_min”
*)
    (*
(**** generate a var table *****)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative old_eval_policy_full_opt_rhs test_groupings;
*)

(* eval TABLE, OLD BDD*)

val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure2 (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));




     (*******************************)
     (*******************************)
     (*******************************)
     (*******************************)
     (*******************************)
     (*******************************)
     (*******************************)


     val policy_order = “["x1";"x2";"z1";"z2";"z3";"z4";"q1";"q2"]”;

val policy_order_mini = “["x1";"x2";"z1"]”;

     
val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order_mini 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));




val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order_mini 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));







Definition simp_tables2_def:
  (simp_tables2 [] s = ([], s)) ∧
  (simp_tables2 (t::tbll) s = 
   (let t' = simp_table t s in
      ( case t' of
        | [([True], st , state s'')] => 
            let (rest_tables, fin_st) = simp_tables2 tbll (SOME s'') in
            (rest_tables, fin_st)
        | _ => 
            let (rest_tables, fin_ste) = simp_tables2 tbll NONE in
            (t'::rest_tables, s)  (* return current state s when we break the pattern *)
      )
   )
  )
End




Definition simp_tables_wrapper2_def:
  simp_tables_wrapper2 ((tbll: 'a var_table_list), st_in) =
  case simp_tables2 tbll (SOME st_in) of
  | (tbls, SOME st_upd) => (tbls, st_upd)
  | (tbls, NONE) => (tbll, st_in)
                    (* if returns none, then problem happened while simplyfing, so we return the whole table*)
End





Definition final_tbll2_def:
  (final_tbll2 ([]: 'a var_table_list) st_in = NONE) ∧
  (final_tbll2 [[([True], s', action a)]] st_in =
  if (s' = st_in) then SOME (action a) else NONE) ∧
  (final_tbll2 _ st_in = NONE)
End





Definition final_tables2_def:
  final_tables2 (tbll, st_in) =
  final_tbll2 tbll st_in
End



Definition table_structure2_def:
  table_structure2 =
  <|
    sem := sem_tables;
    sub := mk_substitute_tables;
    simp := simp_tables_wrapper2;
    final := final_tables2;
    fv := fv_tables;
  |>
End


Definition simp_policy2_def:
  (simp_policy2 [] = []) ∧
  (simp_policy2 ((p,a)::policy) = 
   (let p' = simp_pred p in
      ( case p' of
        | True => [(p',a)]
        | False => (simp_policy2 policy)
        | _ => (p',a)::(simp_policy2 policy)
      )
   )
  )
End


Definition final_policy2_def:
  (final_policy2 ([(True, a)]: 'a policy) = SOME a) ∧
  (final_policy2 (_) = NONE)
End




Definition policy_structure2_def:
  policy_structure2 =
  <|
    sem := sem_policy;
    sub := mk_substitute_policy;
    simp := simp_policy2;
    final := final_policy2;
    fv := fv_policy;
  |>
End   
        
(*
val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 4 3))”;

val is_small_packet1 = “(arithm_le (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 500 16))”;
val is_small_packet2 = “(arithm_le (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 400 16))”;

val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(bdd_utilsLib.make_bv 200 8))”;

val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 8 4))”;



val policy_me =   “[("x", ^is_high_priority);
                    ("y", ^is_medium_priority);
                    ("z1", ^is_small_packet1);
                    ("z2", ^is_small_packet2);
                    ("w", ^is_young_packet);
                    ("q", ^is_control_type);
                    ("r", ^is_data_type)]”;

val policy_full_order = “[("a",["x";"y"]);
                          ("b",["z1";"z2"]);
                          ("c",["w"]);
                          ("d",["q";"r"])]”;

val policy_order = “["x";"y";"z1";"z2";"w";"q";"r"]”;

(* Rule 1: High priority small control packets - expedited forwarding *)
val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_small_packet1) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

(* Rule 2: High priority data packets *)
val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_data_type),
                           action ("fwd",[1])):single_rule”;

(* Rule 3: Medium priority young packets *)
val arith_policy_rule3 = “(arith_and (arith_a ^is_medium_priority) (arith_a ^is_young_packet),
                           action ("fwd",[2])):single_rule”;

(* Rule 3: Medium priority young packets *)
val arith_policy_rule4 = “((arith_a ^is_small_packet2),
                           action ("fwd",[3])):single_rule”;


(* Default forward rule *)
val arith_policy_rule_default = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule4;
                       ^arith_policy_rule_default]:single_rule list”;





val policy_order = “["x";"y";"z1";"z2";"w";"q";"r"]”;

val policy_order_mini = “["x";"y";"z1";"z2";"w";"q";"r"]”;

     
val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure2 (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order_mini 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));




val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure2 (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order_mini 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));

*)








                       
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure2 (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));



(**** generate a var table *****)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative old_eval_policy_full_opt_rhs test_groupings;


(* eval TABLE, OLD BDD*)

val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure2 (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));





(*


val test_pd_type = “[("h", type_record [("srcPort", type_length 16);
                                        ("dstPort", type_length 16);
                                        ("srcNAT", type_length 16);
                                        ("dstNAT", type_length 16)])]”;

(************************************************)
(* rule 1 *)

val is_srcPort_le_57222 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;
val is_srcPort_ge_57222 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;

val is_dstPort_le_53 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;
val is_dstPort_ge_53 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;

val is_srcNAT_le_54587 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54587 16))”;
val is_srcNAT_ge_54587 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54587 16))”;

val is_dstNAT_le_53 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 53 16))”;
val is_dstNAT_ge_53 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 53 16))”;


val arith_policy_rule1 = “((arith_and (arith_a ^is_srcPort_le_57222)
                          (arith_and (arith_a ^is_srcPort_ge_57222)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_54587)
                          (arith_and (arith_a ^is_srcNAT_ge_54587)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 2 *)

val is_srcPort_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcPort_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstPort_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstPort_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;

val is_srcNAT_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcNAT_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstNAT_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstNAT_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;


val arith_policy_rule2 = “((arith_and (arith_a ^is_srcPort_le_56258)
                          (arith_and (arith_a ^is_srcPort_ge_56258)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_56258)
                          (arith_and (arith_a ^is_srcNAT_ge_56258)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 3 *)

val is_srcPort_le_6881 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;
val is_srcPort_ge_6881 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;

val is_dstPort_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstPort_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;

val is_srcNAT_le_43265 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;
val is_srcNAT_ge_43265 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;

val is_dstNAT_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstNAT_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;


val arith_policy_rule3 = “((arith_and (arith_a ^is_srcPort_le_6881)
                          (arith_and (arith_a ^is_srcPort_ge_6881)
                          (arith_and (arith_a ^is_dstPort_le_50321)
                          (arith_and (arith_a ^is_dstPort_ge_50321)
                          (arith_and (arith_a ^is_srcNAT_le_43265)
                          (arith_and (arith_a ^is_srcNAT_ge_43265)
                          (arith_and (arith_a ^is_dstNAT_le_50321)
                                   (arith_a ^is_dstNAT_ge_50321)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 4 *)

val is_srcPort_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcPort_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;

val is_srcNAT_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcNAT_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;


val arith_policy_rule4 = “((arith_and (arith_a ^is_srcPort_le_50553)
                          (arith_and (arith_a ^is_srcPort_ge_50553)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_50553)
                          (arith_and (arith_a ^is_srcNAT_ge_50553)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 5 *)

val is_srcPort_le_50002 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;
val is_srcPort_ge_50002 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;

val is_dstPort_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstPort_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;

val is_srcNAT_le_45848 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;
val is_srcNAT_ge_45848 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;

val is_dstNAT_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstNAT_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;


val arith_policy_rule5 = “((arith_and (arith_a ^is_srcPort_le_50002)
                          (arith_and (arith_a ^is_srcPort_ge_50002)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_45848)
                          (arith_and (arith_a ^is_srcNAT_ge_45848)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;

(* Combined arith policy list *)
val arith_policy = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule5;
    ^arith_policy_rule_default
]:single_rule list”;



(* Combined policy mapping *)
val policy_me =   “[
    ("is_srcPort_le_57222", ^is_srcPort_le_57222);
    ("is_srcPort_ge_57222", ^is_srcPort_ge_57222);
    ("is_dstPort_le_53", ^is_dstPort_le_53);
    ("is_dstPort_ge_53", ^is_dstPort_ge_53);
    ("is_srcNAT_le_54587", ^is_srcNAT_le_54587);
    ("is_srcNAT_ge_54587", ^is_srcNAT_ge_54587);
    ("is_dstNAT_le_53", ^is_dstNAT_le_53);
    ("is_dstNAT_ge_53", ^is_dstNAT_ge_53);
    ("is_srcPort_le_56258", ^is_srcPort_le_56258);
    ("is_srcPort_ge_56258", ^is_srcPort_ge_56258);
    ("is_dstPort_le_3389", ^is_dstPort_le_3389);
    ("is_dstPort_ge_3389", ^is_dstPort_ge_3389);
    ("is_srcNAT_le_56258", ^is_srcNAT_le_56258);
    ("is_srcNAT_ge_56258", ^is_srcNAT_ge_56258);
    ("is_dstNAT_le_3389", ^is_dstNAT_le_3389);
    ("is_dstNAT_ge_3389", ^is_dstNAT_ge_3389);
    ("is_srcPort_le_6881", ^is_srcPort_le_6881);
    ("is_srcPort_ge_6881", ^is_srcPort_ge_6881);
    ("is_dstPort_le_50321", ^is_dstPort_le_50321);
    ("is_dstPort_ge_50321", ^is_dstPort_ge_50321);
    ("is_srcNAT_le_43265", ^is_srcNAT_le_43265);
    ("is_srcNAT_ge_43265", ^is_srcNAT_ge_43265);
    ("is_dstNAT_le_50321", ^is_dstNAT_le_50321);
    ("is_dstNAT_ge_50321", ^is_dstNAT_ge_50321);
    ("is_srcPort_le_50553", ^is_srcPort_le_50553);
    ("is_srcPort_ge_50553", ^is_srcPort_ge_50553);
    ("is_srcNAT_le_50553", ^is_srcNAT_le_50553);
    ("is_srcNAT_ge_50553", ^is_srcNAT_ge_50553);
    ("is_srcPort_le_50002", ^is_srcPort_le_50002);
    ("is_srcPort_ge_50002", ^is_srcPort_ge_50002);
    ("is_dstPort_le_443", ^is_dstPort_le_443);
    ("is_dstPort_ge_443", ^is_dstPort_ge_443);
    ("is_srcNAT_le_45848", ^is_srcNAT_le_45848);
    ("is_srcNAT_ge_45848", ^is_srcNAT_ge_45848);
    ("is_dstNAT_le_443", ^is_dstNAT_le_443);
    ("is_dstNAT_ge_443", ^is_dstNAT_ge_443);
]”;

(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321";"is_dstPort_le_443";"is_dstPort_ge_443"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553";"is_srcNAT_le_45848";"is_srcNAT_ge_45848"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321";"is_dstNAT_le_443";"is_dstNAT_ge_443"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002"; "is_srcPort_ge_50002"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_dstPort_le_443"; "is_dstPort_ge_443"; "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; "is_srcNAT_le_45848"; "is_srcNAT_ge_45848"; "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321"; "is_dstNAT_le_443"; "is_dstNAT_ge_443"]”;


*)
