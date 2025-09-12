open HolKernel boolLib liteLib simpLib Parse bossLib pairLib;
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
     
open tables_spec_newTheory;

open bdd_utilsLib;
open fwd_proofLib;

val _ = new_theory "profiling_proof";

(*






val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 4 3))”;

val is_size_packet1 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 30000 16))”;
val is_size_packet2 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 27000 16))”;
val is_size_packet3 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 25000 16))”;
val is_size_packet4 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 23000 16))”;


val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(bdd_utilsLib.make_bv 200 8))”;

val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 8 4))”;



val policy_me =   “[("x1", ^is_high_priority);
                    ("x2", ^is_medium_priority);

                    ("z1", ^is_size_packet1);
                    ("z2", ^is_size_packet2);
                    ("z3", ^is_size_packet3);
                    ("z4", ^is_size_packet4);

                    ("q1", ^is_control_type);
                    ("q2", ^is_data_type)]”;

val policy_full_order = “[("a",["x1";"x2"]);
                          ("b",["z1";"z2";"z3";"z4"]);
                          ("d",["q1";"q2"])]”;

val policy_order = “["x1";"x2";"z1";"z2";"z3";"z4";"q1";"q2"]”;

val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet2),
                           action ("fwd",[1])):single_rule”;

val arith_policy_rule3 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet3),
                           action ("fwd",[2])):single_rule”;

val arith_policy_rule4 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet4),
                           action ("fwd",[3])):single_rule”;

val arith_policy_rule5 = “(arith_and (arith_a ^is_medium_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_data_type)),
                           action ("fwd_priority",[1; 4])):single_rule”;




(* Default forward rule *)
val arith_policy_rule_default = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule4;
                       ^arith_policy_rule5;
                       ^arith_policy_rule_default]:single_rule list”;








(*convert arith policy to var policy*)        
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));
                       

val eval_policy_full_opt_old = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                 ^policy_order 1”;




val eval_policy_full_opt_new = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                 ^policy_order 1”;



                                 




(*____________________________*)


(*

Definition merge_BDD_new_def:
  merge_BDD_new (BDD:('a,'b) BDD) n [] = BDD ∧
  merge_BDD_new (BDD:('a,'b) BDD) n (n'::nl) = 
  (case mergable BDD n n' of
   | F => merge_BDD_new BDD n nl
   | T => merge_BDD_new (merge BDD n n') n nl
  )
End


Definition operate_opt1_new_def:
  (operate_opt1_new (BDD:('a,'b) BDD)  ([]:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt1_new BDD (n::rest) = (operate_opt1_new (merge_BDD_new BDD n rest) rest) )   
End
        

Definition bdd_optminzation1_new_def:
  bdd_optminzation1_new (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt1_new BDD all_nodes 
End




        
(* eliminate part *) 
Definition eliminate_BDD_new_def:
  eliminate_BDD_new (BDD:('a,'b) BDD) n [] = BDD ∧
  eliminate_BDD_new (BDD:('a,'b) BDD) n (n'::nl) = 
  (case eliminable BDD n' n of
   | F => eliminate_BDD_new BDD n nl
   | T => eliminate_BDD_new (merge BDD n' n) n nl
  )
End

Definition operate_opt2_new_def:
  (operate_opt2_new (BDD:('a,'b) BDD) ([]:num list)  = (BDD:('a,'b) BDD)) ∧
  (operate_opt2_new BDD (n::rest)  =  (operate_opt2_new (eliminate_BDD_new BDD n rest) rest )) 
End
  
Definition bdd_optminzation2_new_def:
  bdd_optminzation2_new (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt2_new BDD all_nodes
End


Definition bdd_one_round_new_def:
  bdd_one_round_new BDD = bdd_optminzation1_new (bdd_optminzation2_new BDD)
End





Definition bdd_full_optimize_new_def:
  bdd_full_optimize_new (BDD:('a,'b) BDD) =
  case bdd_one_round_new BDD = BDD of
  | T => BDD
  | F => bdd_full_optimize_new  (bdd_one_round_new BDD)                                      
Termination
        
cheat
End


        
Definition mk_BDDPred_opt_new_def:
  (mk_BDDPred_opt_new rec (BDD:('a,'b) BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred_opt_new rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt_new rec (bdd_full_optimize_new BDD') (x::l) xs c'
   | NONE => NONE 
  )
End






val eval_policy_full_opt_new = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                 ^policy_order 1”;

*)



Definition merge_BDD_new_def:
  merge_BDD_new (BDD:('a,'b) BDD) n [] = BDD ∧
  merge_BDD_new (BDD:('a,'b) BDD) n (n'::nl) = 
  (case mergable BDD n n' of
   | F => merge_BDD_new BDD n nl
   | T => merge_BDD_new (merge BDD n n') n nl
  )
End


Definition operate_opt1_new_def:
  (operate_opt1_new (BDD:('a,'b) BDD)  ([]:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt1_new BDD (n::rest) = (operate_opt1_new (merge_BDD_new BDD n rest) rest) )   
End
        
Definition is_termn_def:
  is_termn (termn _) = T ∧
  is_termn (_) = F
End

Definition is_ntl_def:
  is_ntl (non_termn (NONE, _)) = T ∧
  is_ntl (_) = F
End



Definition is_intern_def:
  is_intern (non_termn (SOME _ , _)) = T ∧
  is_intern (_) = F
End

Definition is_intern_x_def:
  is_intern_x (non_termn (SOME x' , _)) x = (x=x') ∧
  is_intern_x (_) x = F
End


Definition bdd_optminzation1_internal_new_def:
  (bdd_optminzation1_internal_new (BDD:('a,'b) BDD) [] = BDD) /\
  (bdd_optminzation1_internal_new (BDD:('a,'b) BDD) (x::xl)=
  let (r,edges,labels) = BDD in
    
    let labeled_nodes = MAP FST (FILTER (\(n,b). is_intern_x b x) labels) in
      let BDD' = operate_opt1_new BDD labeled_nodes in 
        bdd_optminzation1_internal_new BDD' (xl)
  )
End





Definition bdd_optminzation1_new_def:
  bdd_optminzation1_new (BDD:('a,'b) BDD) order =
  let (r,edges,labels) = BDD in
    
    let tl_nodes = MAP FST (FILTER (\(n,b). is_termn b) labels) in
      let (r',edges',labels') = operate_opt1_new BDD tl_nodes in 
        
        let ntl_nodes = MAP FST (FILTER (\(n,b). is_ntl b) labels') in 
          let (r'',edges'',labels'') = operate_opt1_new (r',edges',labels') ntl_nodes in 
              bdd_optminzation1_internal_new (r'',edges'',labels'') (order)
End






        
(* eliminate part *) 
Definition eliminate_BDD_new_def:
  eliminate_BDD_new (BDD:('a,'b) BDD) n [] = BDD ∧
  eliminate_BDD_new (BDD:('a,'b) BDD) n (n'::nl) = 
  (case eliminable BDD n' n of
   | F => eliminate_BDD_new BDD n nl
   | T => eliminate_BDD_new (merge BDD n' n) n nl
  )
End

Definition operate_opt2_new_def:
  (operate_opt2_new (BDD:('a,'b) BDD) ([]:num list)  = (BDD:('a,'b) BDD)) ∧
  (operate_opt2_new BDD (n::rest)  =  (operate_opt2_new (eliminate_BDD_new BDD n rest) rest )) 
End
  
Definition bdd_optminzation2_new_def:
  bdd_optminzation2_new (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt2_new BDD all_nodes
End


Definition bdd_one_round_new_def:
  bdd_one_round_new BDD order = bdd_optminzation1_new (bdd_optminzation2_new BDD) order
End





Definition bdd_full_optimize_new_def:
  bdd_full_optimize_new (BDD:('a,'b) BDD) order =
  case bdd_one_round_new BDD order = BDD of
  | T => BDD
  | F => bdd_full_optimize_new  (bdd_one_round_new BDD order) order                                     
Termination
        
cheat
End


        
Definition mk_BDDPred_opt_new_def:
  (mk_BDDPred_opt_new rec (BDD:('a,'b) BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred_opt_new rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt_new rec (bdd_full_optimize_new BDD' (x::l)) (x::l) xs c'
   | NONE => NONE 
  )
End


val eval_policy_full_opt_new = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                 ^policy_order 1”;






*)





                                 
val _ = export_theory ();





val _ = type_abbrev("distrub_st", ``:( (string, (num list) option) alist   # num list # num list)``);


Definition update_internals_def:
  (update_internals pre [] n x = []) ∧    
  (update_internals pre (h::internals) n x =
   let (var, node_list_op) =  h in
     (if var ≠ x then
        update_internals (pre++[h]) internals n x 
      else
        (
        case node_list_op of
        | SOME l =>  pre++[(var, SOME (n::l))]++internals
        | NONE => pre++[(var, SOME [n])]++internals                            
        )
     )
  )
End

          
Definition distrubute_labels_def:
  (distrubute_labels [] (acc:distrub_st) = acc) ∧
  (distrubute_labels ((n,lbl)::labels) (internals, ntl, tl) =
   case lbl of
   | termn _ => distrubute_labels labels (internals, ntl, n::tl)
   | non_termn (NONE , _) => distrubute_labels labels (internals, n::ntl, tl)
   | non_termn (SOME x , _)  => distrubute_labels labels (update_internals [] internals n x, ntl, tl)
  )
End





           
Definition bdd_distribute_def:
  bdd_distribute (BDD:('a,'b) BDD) order =
  let (r,edges,labels) = BDD in
    let internals_init = MAP (\x. (x,NONE)) order in
      distrubute_labels labels (internals_init, [],[])
End



Definition merge_safe_def:
  merge_safe (BDD:('a,'b) BDD) n n' =
  if mergable BDD n n' then
    merge BDD n' n
   else
    BDD
End


Definition eliminate_safe_def:
  eliminate_safe (BDD:('a,'b) BDD) n =
  case eliminable BDD n  of
  | SOME n' =>  merge BDD n' n
  | NONE => BDD
End



(* can be improved more *)

(* can be improved more *)
Definition optimize_node_def:
  (optimize_node (BDD:('a,'b) BDD) n [] = eliminate_safe BDD n) ∧

  (optimize_node BDD n (n'::nl) = 
    case eliminable BDD n of
  | SOME n' =>  eliminate_safe (BDD:('a,'b) BDD) n
  | NONE => optimize_node (merge_safe BDD n n') n nl)
End

        


Definition optimize_layer_def:
  (optimize_layer (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_layer BDD  (n::nl)=
   optimize_layer (optimize_node BDD n nl) nl
  )
End

        
Definition optimize_internals_def:
  (optimize_internals (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_internals BDD  ((var,NONE)::l) = optimize_internals BDD l) /\

  (optimize_internals BDD  ((var,SOME nl)::l)=
   let BDD' = optimize_layer BDD  nl in
       optimize_internals BDD' l
  )
End



        
Definition optimize_bdd_def:
  optimize_bdd (BDD:('a,'b) BDD) order =
  let (internals,ntl,tl) = bdd_distribute (BDD:('a,'b) BDD) order in
    let BDD1 = optimize_layer BDD tl in
      let BDD2 = optimize_layer BDD1 ntl in
        optimize_internals BDD2 internals
End
                        



Definition mk_BDDPred_opt_new_def:
  (mk_BDDPred_opt_new rec (BDD:('a,'b) BDD) l [] c = SOME (optimize_bdd BDD l)) ∧
  (mk_BDDPred_opt_new rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt_new rec (optimize_bdd BDD' (x::l)) (x::l) xs c'
   | NONE => NONE 
  )
End




val eval_policy_full_opt_old = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                 ^policy_order 1”;

                                 
val eval_policy_full_opt_new = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) []
                                     ^policy_order 1”;

                                     
val bdd_eval =  (optionSyntax.dest_some (rhs (concl eval_policy_full_opt_new)));





        val test_groupings = rhs(concl(EVAL policy_full_order));
        val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative bdd_eval test_groupings;

val eval_table_full_opt_auto_old = EVAL “mk_BDDPred_opt table_structure_new (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
val eval_table_full_opt_auto_new = EVAL “mk_BDDPred_opt_new table_structure_new (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;












    
val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 4 3))”;

val is_size_packet1 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 30000 16))”;
val is_size_packet2 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 27000 16))”;
val is_size_packet3 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 25000 16))”;
val is_size_packet4 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 23000 16))”;


val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(bdd_utilsLib.make_bv 200 8))”;

val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 8 4))”;



val policy_me =   “[("x1", ^is_high_priority);
                    ("x2", ^is_medium_priority);

                    ("z1", ^is_size_packet1);
                    ("z2", ^is_size_packet2);
                    ("z3", ^is_size_packet3);
                    ("z4", ^is_size_packet4);

                    ("q1", ^is_control_type);
                    ("q2", ^is_data_type)]”;

val policy_full_order = “[("a",["x1";"x2"]);
                          ("b",["z1";"z2";"z3";"z4"]);
                          ("d",["q1";"q2"])]”;

val policy_order = “["x1";"x2";"z1";"z2";"z3";"z4";"q1";"q2"]”;

val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet2),
                           action ("fwd",[1])):single_rule”;

val arith_policy_rule3 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet3),
                           action ("fwd",[2])):single_rule”;

val arith_policy_rule4 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet4),
                           action ("fwd",[3])):single_rule”;

val arith_policy_rule5 = “(arith_and (arith_a ^is_medium_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_data_type)),
                           action ("fwd_priority",[1; 4])):single_rule”;




(* Default forward rule *)
val arith_policy_rule_default = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule4;
                       ^arith_policy_rule5;
                       ^arith_policy_rule_default]:single_rule list”;

(**************************************************)


    val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
    val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));

