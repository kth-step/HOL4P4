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



val _ = type_abbrev("distrub_st", ``:( (string, (num list) option) alist   # num list # num list)``);



(*

Definition eliminable_new_def:
  eliminable_new ((r,edges,labels):('a,'b)BDD) n = 
    case ALOOKUP edges n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           has_parent edges n1 n
        then SOME n1
        else NONE
    | NONE => NONE
End



Definition eliminable_projection_def:
  eliminable_projection edges_proj n = 
    case ALOOKUP edges_proj n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           n ≠ 0n ∧
           has_parent edges_proj n1 n 
        then SOME n1
        else NONE
    | NONE => NONE
End


Definition mergable_projection_def:        
  mergable_projection edges_proj labels_proj n n' = 
  (n≠n' ∧ ALOOKUP edges_proj n = ALOOKUP edges_proj n' ∧
   eq_vars_in_labels labels_proj n n' ∧ ALOOKUP labels_proj n'  ≠ NONE )
End



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
    (T, merge BDD n n')
   else
    (F, BDD)
End


Definition eliminate_safe_def:
  eliminate_safe (BDD:('a,'b) BDD) n =
  case eliminable_new BDD n  of
  | SOME n' =>  (T, merge BDD n' n)
  | NONE => (F,BDD)
End





Definition optimize_node_def:
  (optimize_node edges_proj labels_proj (BDD:('a,'b) BDD) n [] = SND (eliminate_safe BDD n)) ∧
  
  (optimize_node edges_proj labels_proj BDD n (n'::nl) = 
   case eliminable_projection edges_proj n of
   | SOME n' =>  SND (eliminate_safe BDD n)
   | NONE => (
     case mergable_projection edges_proj labels_proj n' n of
     | T => ( case merge_safe BDD n' n of
              | (T, BDD') => BDD'
              | (F, BDD') => optimize_node edges_proj labels_proj BDD n nl
            )
            
     | F => optimize_node edges_proj labels_proj BDD n nl)
  )
End

        


Definition optimize_layer_def:
  (optimize_layer edges_proj labels_proj (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_layer edges_proj labels_proj BDD  (n::nl)=
   optimize_layer edges_proj labels_proj (optimize_node edges_proj labels_proj BDD n nl) nl
  )
End


Definition project_edges_to_def:
  project_edges_to ((r, edges,labels):('a,'b) BDD) nl = 
    MAP (\n. (n,THE(ALOOKUP edges n))) nl
End

Definition project_labels_to_def:
  project_labels_to ((r, edges,labels):('a,'b) BDD) nl = 
    MAP (\n. (n,THE(ALOOKUP labels n))) nl
End



Definition optimize_internals_def:
  (optimize_internals (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_internals BDD  ((var,NONE)::l) = optimize_internals BDD l) /\

  (optimize_internals BDD  ((var,SOME nl)::l)=
    let edges_proj = project_edges_to BDD nl in
     let labels_proj = project_labels_to BDD nl in
      let BDD' = optimize_layer edges_proj labels_proj BDD  nl in
         optimize_internals BDD' l
  )
End



        
Definition optimize_bdd_def:
  optimize_bdd (BDD:('a,'b) BDD) order =
  let (internals,ntl,tl) = bdd_distribute (BDD:('a,'b) BDD) order in
    let labels_proj_tl = project_labels_to BDD tl in (* for terminals *)
      let labels_proj_ntl = project_labels_to BDD ntl in (* for terminals *)
        let BDD1 = optimize_layer [] labels_proj_tl BDD tl in
          let BDD2 = optimize_layer [] labels_proj_ntl BDD1 ntl in
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



(**************************************************)


    val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
    val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));



*)






val _ = export_theory ();


