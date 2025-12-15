open HolKernel Parse boolLib bossLib;
open optionTheory bdd_sptrees_genTheory pairTheory bdd_genTheory policy_specTheory pred_specTheory;     
open preamble basis ml_translatorLib ;

open miscTheory ml_translatorTheory ListProgTheory ;
open fromSexpTheory;


     
val _ = new_theory "bdd_trans_Prog";


        
val _ = translation_extends "basisProg"
val _ = intLib.deprecate_int();

(* translation of sp_optimize_bdd*)

val r = translate lrnext_def;
val r = translate update_internals_def;
val r = translate distrubute_labels_def;
val r = translate foldi_def;
val r = translate toAList_def;
val r = translate sp_bdd_distribute_def;



val r = translate insert_def;
val r = translate mk_BN_def;
val r = translate mk_BS_def;
val r = translate mapi0_def;
val r = translate mapi_def;
val r = translate lookup_def;
val r = translate delete_def;
val r = translate sp_eq_vars_in_labels_def;
val r = translate sp_mergable_def;
val r = translate sp_merge_edges_def;
val r = translate sp_merge_def;


val r = translate sp_merge_safe_def;
val r = translate sp_optimize_node_leaf_def
val r = translate sp_optimize_layer_leaf_def;


val r = translate sp_eliminable_def;
val r = translate sp_eliminate_safe_def;

val r = translate sp_optimize_node_def;
val r = translate sp_optimize_layer_def;
val r = translate sp_optimize_internals_def;

val r = translate sp_optimize_bdd_def;


(* translation of sp_body_of_mk *)
val r = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate (get_leaves_list_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate getLeaves_def;

val r = translate sp_getLabels_def;
val r = translate extract_nontermn_def;
val r = translate determine_termn_def;
val r = translate sp_determine_termn_list_def;
val r = translate sp_mk_new_labels_def;
val r = translate sp_mk_new_edges_def;
val r = translate sp_body_of_mk_def;

(* translation of sp_mk_BDDPred_opt *)

val r = translate INDEX_FIND_def;  
val r = translate min_idx_till_def;
val r = translate sem_pred_def;
val r = translate check_sem_pred_def;
val r = translate sem_policy_def;


val r = translate mk_substitute_pred_def;
val r = translate mk_substitute_policy_def;

val r = translate simp_pred_def;
val r = translate simp_policy_def;

val r = translate listTheory.EVERY_DEF;
val r = translate rich_listTheory.SEG;
val r = translate pre_are_fail_def;
val r = translate final_policy_def;

Theorem final_policy_cake_trans:
  final_policy_side v4
Proof
  rw [fetch "-" "final_policy_side_def"] >>
  rw [fetch "-" "pre_are_fail_side_def"] >>
  rw [Once (fetch "-" "seg_side_def")] >>
  fs[min_idx_till_def] >> cheat
QED


val _ = final_policy_cake_trans |> update_precondition;


        
val r = translate fv_pred_def;
val r = translate fv_policy_def;
    
val r = ml_translatorLib.register_type ``:((pred # 'a) list, 'b) decision_structure``;
val r = translate policy_structure_def;


   
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

Definition sp_mk_BDD_policy_def:
  sp_mk_BDD_policy (var_policy: action_policy_type ) policy_order =
  sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, var_policy)) LN) [] policy_order 1n
End

val r = translate sp_mk_BDDPred_opt_def;
val r = translate sp_mk_BDD_policy_def;
             


(*****************************************************)


val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


        

Definition policy_order_test_def:
 policy_order_test = ["x";"y";"z"]
End

val r = translate policy_order_test_def;

Definition policy_content_test_def:
  policy_content_test = [
    (Var "x", action ("allow",[1]));
    (And (Var "y") (Var "z"), action ("allow",[2]));
    (True, action ("drop",[]))
  ]:action_policy_type
End

val r = translate policy_content_test_def;

                       
Definition main_hol4_def:
  main_hol4 =
    sp_mk_BDD_policy policy_content_test  policy_order_test
End

        
val r = translate main_hol4_def;
 
val res = append_prog o process_topdecs $ 
                      ‘fun main () =
                       let
                        val args = CommandLine.arguments()
                        in
                      (case main_hol4 of
                       None => TextIO.print "No BDD can be created \n"
                       | Some bdd => TextIO.print "SOME \n")
                      end ;’
                     ; 


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                                

val _ = astToSexprLib.write_ast_to_file "test_bdd.sexp" prog;










(************************)

val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 200);



val var_pred = “ Or (And (Var "x") (Not (Var "y"))) (And (Not (Var "a")) (Var "b")) ”;
val var_pred2 = “ Or (And (Var "c") (Not (Var "d"))) (And (Not (Var "e")) (Var "f")) ”;
val var_pred3 = “ Or ^var_pred ^var_pred2 ”;


     
EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["a";"b";"c"; "d"; "f"; "g"; "x"; "y"] 1”;

EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["a";"b";"c"; "d"; "x"; "y"; "f"; "e"] 1”;

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

val rule1 = “(^var_pred3 , action ("allow",[1]: num list)):action_rule_type”;
val rule2 = “((Var "k") , action ("allow",[2]: num list)):action_rule_type”;
val rule3 = “((Var "o") , action ("allow",[3]: num list)):action_rule_type”;

val arith_policy_rule_default = “(True, action ("drop", []: num list)):action_rule_type”;


val arith_policy = “[
    ^rule1;
    ^rule2;
    ^arith_policy_rule_default
                     ]: action_policy_type”;




Definition toAList_BDD_edges_def:
  toAList_BDD_edges (r,edges,labels) = toSortedAList edges
End

Definition toAList_BDD_labels_def:
  toAList_BDD_labels (r,edges,labels) = toSortedAList labels
End

Definition BDD_root_is_def:
  BDD_root_is (r,edges,labels) = r
End


val a = (optionSyntax.dest_some (rhs ( concl (EVAL “ (sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, ^arith_policy)) LN) []
     ["o";"k";"x";"y";"a";"b";"c";"d"]
     1)”))));


val edges_list = rhs ( concl (EVAL “ toAList_BDD_edges  ^a ”));
val labels_list = rhs ( concl (EVAL “ toAList_BDD_labels  ^a ”));





     



Definition test_bdd_def:
  test_bdd = SOME ^edges_list
End


val r = translate test_bdd_def;

val _ = (max_print_depth := 200);



(************************************************)

open HolKernel Parse boolLib bossLib;
open optionTheory bdd_sptrees_genTheory pairTheory bdd_genTheory policy_specTheory pred_specTheory;     
open preamble basis ml_translatorLib ;

open miscTheory ml_translatorTheory ListProgTheory ;
open fromSexpTheory;


val _ = translation_extends "basisProg"
val _ = intLib.deprecate_int();

                               
(* print edges *)     

(*
   
Definition test_list_edges_def:
  test_list_edges = SOME ([(1,2,3);(4,5,6)]:edges)
End

val r = translate test_list_edges_def;
*)

        
val res = append_prog o process_topdecs $ 
‘fun print_tuple_list xs =
  let
    fun print_elem e =
    let
        val (a, bc) = e ;
        val (b, c) = bc
      in
        TextIO.print "(";
        TextIO.print (Int.toString a);
        TextIO.print ",";
        TextIO.print (Int.toString b);
        TextIO.print ",";
        TextIO.print (Int.toString c);
        TextIO.print ")"
      end

    fun loop xs =
      case xs of
          [] => TextIO.print " Here is the end "
        | [x] => print_elem x
        | x::rest =>
            (print_elem x;
             TextIO.print ", ";
             loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
          end’;



(*
  
val res = append_prog o process_topdecs $ 
‘fun main () =
                       let
                       val args = CommandLine.arguments()
                       in
                          (case test_list_edges of
                            None => TextIO.print "No BDD can be created \n"
                           | Some l =>  print_tuple_list l;
                                        TextIO.print "\n";
                           )
                         end ;’
; 


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                                

val _ = astToSexprLib.write_ast_to_file "test_bdd.sexp" prog;
*)


(*(((string#num list) action_expr) policy, (string#num list) action_expr) labelings)*)

(*
val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 200);
*)




(* print labels *)
        
val res = append_prog o process_topdecs $ 
‘fun print_string cs =
  let fun loop xs =
        case xs of
            [] => ()
          | c::rest => (TextIO.print (String.str c); loop rest)
  in loop cs end;’; 



val res = append_prog o process_topdecs $ 
‘
fun print_numl nl =
let fun loop l =
    case l of
      [] => ()
    | [n] => (TextIO.print (Int.toString n))
    | n::rest => (TextIO.print (Int.toString n); TextIO.print "; "; loop rest)
in
  
  (TextIO.print "[";
  loop nl;
  TextIO.print "]")
      
      end;’; 

  
 
val res = append_prog o process_topdecs $ 
‘
fun print_pred p =
  case p of
      True_1 => TextIO.print "True"
    | False_1 => TextIO.print "False"
    | Var cs => (TextIO.print "Var \""; print_string cs; TextIO.print "\"")
    | Not q => (TextIO.print "Not ("; print_pred q; TextIO.print ")")
    | And a b => (TextIO.print "And (";
                  print_pred a;
                  TextIO.print ") (";
                  print_pred b; TextIO.print ")")
    | Or a b => (TextIO.print "Or (";
                  print_pred a;
                  TextIO.print ") (";
                  print_pred b; TextIO.print ")")
    | Implies a b => (TextIO.print "Implies (";
                  print_pred a;
                  TextIO.print ") (";
                  print_pred b; TextIO.print ")");
’; 


val res = append_prog o process_topdecs $ 
‘
fun print_action a = 
case a of 
(Action (cs,nl)) =>
      (TextIO.print "action (\"";
       print_string cs;
       TextIO.print "\",";
       print_numl nl ;
       TextIO.print ")")
| (State i) =>
      (TextIO.print "state(";
       TextIO.print (Int.toString i);
       TextIO.print ")");
’; 


val res = append_prog o process_topdecs $    
‘fun print_pair (p, act) =
  ( TextIO.print "(";
    print_pred p;
    TextIO.print ", ";
    print_action act;
    TextIO.print ")"
  );’; 


val res = append_prog o process_topdecs $   
‘fun print_list_pairs xs =
  let
    fun loop xs =
      case xs of
          [] => ()
        | [x] => print_pair x
        | x::rest =>
            ( print_pair x; TextIO.print ", "; loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
  end;’;



val res = append_prog o process_topdecs $   
‘fun print_pair_termin (act, p) =
 ( TextIO.print "(";
   print_action act;
    TextIO.print ", ";
    print_list_pairs p;
    TextIO.print ")"
  );
’;



val res = append_prog o process_topdecs $ 
‘fun print_label lab =
  case lab of
    Non_termn (optname, lst) =>
      (TextIO.print "non_termn (";
       (case optname of
          None => TextIO.print "NONE"
          | Some cs => (TextIO.print "SOME \""; print_string cs; TextIO.print "\"")
       );
       TextIO.print ", ";
       print_list_pairs lst;
       TextIO.print ")")
  | Termn fin =>
      (TextIO.print "termn (";
       print_pair_termin fin;
       TextIO.print ")");
’;



val res = append_prog o process_topdecs $ 
‘fun print_list_label xs =
  let
    fun loop xs =
      case xs of
          [] => ()
        | [x] => (TextIO.print "(";
                  TextIO.print (Int.toString (fst x));
                  TextIO.print ", ";
                  print_label (snd x);
                  TextIO.print ")")
        | x::rest =>
            (TextIO.print "(";
             TextIO.print (Int.toString (fst x));
             TextIO.print ", ";
             print_label (snd x);
             TextIO.print "); ";
             loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
  end;’;



(*


Definition test_list_labels_def:
  test_list_labels = SOME ([(23,
      termn
        (action ("allow",[1]),
         [(True,action ("allow",[1]));
          (False,action ("allow",[2]));
          (True,action ("drop",[]))]))] :
                           (((string#num list) action_expr) policy, (string#num list) action_expr) labelings)
End



val r = translate test_list_labels_def;


        
val res = append_prog o process_topdecs $ 
‘fun main () =
                       let
                       val args = CommandLine.arguments()
                       in
                          (case test_list_labels  of
                            None => TextIO.print "No BDD can be created \n"
                           | Some l => print_list_label l
                           )
                         end ;’
; 


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                                

val _ = astToSexprLib.write_ast_to_file "test_bdd.sexp" prog;
*)





val _ = export_theory ();
