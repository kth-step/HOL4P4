open HolKernel Parse boolLib bossLib;
open optionTheory bdd_sptrees_genTheory pairTheory bdd_genTheory tables_specTheory tables_spec_oldTheory policy_specTheory pred_specTheory;     
open preamble basis ml_translatorLib ;

open miscTheory ml_translatorTheory ListProgTheory ;
open fromSexpTheory;


     
val _ = new_theory "sptrees_bdd_trans_Prog";

(*)
 val _ = ml_prog_update (open_module "cake_sptrees_bdd_trans_Prog");
*)   
        
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
  Induct_on ‘v4’ >>
  rw [fetch "-" "final_policy_side_def"] >>
  rw [fetch "-" "pre_are_fail_side_def"] >>
  rw [Once (fetch "-" "seg_side_def")] >>
  fs[min_idx_till_def, INDEX_FIND_def] >> cheat
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
             


(***********************************)
(* tables translation  *)

val r = translate sem_var_atom_def;
val r = translate is_atoml_true_def;
val r = translate is_match_row_def;
val r = translate check_all_rows_match_def;
val r = translate match_tbl_def;
val r = translate match_tbll_def;
val r = translate sem_tables_def;

val r = translate mk_substitute_atom_def;
val r = translate mk_substitute_row_def;
val r = translate mk_substitute_tbl_def;
val r = translate mk_substitute_tbll_def;
val r = translate mk_substitute_tables_def;

val r = translate simp_atom_def;
val r = translate is_not_true_var_atom_def;
val r = translate (simp_row_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate simp_table_def;
val r = translate simp_tables_def;
val r = translate simp_tables_wrapper_def;

val r = translate final_row_def;
val r = translate final_tbl_def;
val r = translate final_tbll_def;
val r = translate final_tables_def;

val r = translate fv_atom_def;
val r = translate fv_row_def;
val r = translate fv_tbl_def;
val r = translate fv_tbll_def;  
val r = translate fv_tables_def;
    
val r = translate table_structure_def;

    
val _ = type_abbrev("action_table_type", “:((string# num list) var_table_list # num)”);


    
Definition sp_mk_BDD_table_def:
  sp_mk_BDD_table (var_table: action_table_type) policy_order =
  sp_mk_BDDPred_opt table_structure (0n,LN,insert 0 (non_termn (NONE, var_table)) LN) [] policy_order 1n
End


val r = translate sp_mk_BDD_table_def;

    
(*****************************************************)
(***********  common printing      *******************)
(*****************************************************)

(****************)
(* print edges  *)     
(****************)

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
             TextIO.print "; ";
             loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
          end’;

          
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
      (TextIO.print "state  ";
       TextIO.print (Int.toString i);
       TextIO.print " ");
’; 

      
(*********************************************************)
(***********  policy specific printing *******************)
(*********************************************************)

(****************)
(* print labels *)
(****************)
  

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
            ( print_pair x; TextIO.print "; "; loop rest)
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
             TextIO.print "); \n ";
             loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
  end;’;



val r = translate spts_to_alist_add_pause_def;
val r = translate spt_left_def;
val r = translate spt_right_def;
val r = translate spt_center_def;

val r = translate spts_to_alist_aux_def;
val r = translate spts_to_alist_def;
val r = translate toSortedAList_def;

    

val res = append_prog o process_topdecs $ 
‘
fun print_atom p =
  case p of
      True_2 => TextIO.print "True"
    | False_2 => TextIO.print "False"
    | Var_1 cs => (TextIO.print "Var \""; print_string cs; TextIO.print "\"")
    | Not_1 cs => (TextIO.print "Not \""; print_string cs; TextIO.print "\"")
    | Notfalse => TextIO.print "NotFalse"
    | Nottrue => TextIO.print "NotTrue"
’; 


    
val res = append_prog o process_topdecs $    
‘fun print_al_n_s (atom_l, n_state) =
 let
        
  fun loop xs =
  case xs of
    [] => ()
  | [atom] => print_atom atom
  | atom::rest => (print_atom atom ; TextIO.print "; " ; loop rest)
 in
  ( TextIO.print "([";
    loop atom_l;
    TextIO.print "],";
    TextIO.print (Int.toString (fst n_state));
    TextIO.print ",";
    print_action (snd n_state);
    TextIO.print ")"
  )
  end’; 




val res = append_prog o process_topdecs $   
‘fun print_list_tbl xs =
 let

    fun loop_inner tbl =
      case tbl of
          [] => ()
        | [al_n_s] => print_al_n_s al_n_s 
        | al_n_s::rest => (print_al_n_s al_n_s ; TextIO.print "; " ;  loop_inner rest)
        
    fun loop xs =
      case xs of
          [] => ()
        | [x] => (TextIO.print "[" ; loop_inner x ; TextIO.print "]")
        | x::rest => ( TextIO.print "[" ; loop_inner x ; TextIO.print "]; " ; loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
end;’;



val res = append_prog o process_topdecs $ 
‘fun print_table_label lab =
  case lab of
    Non_termn (optname, lst_n) =>
      (TextIO.print "non_termn (";
       (case optname of
          None => TextIO.print "NONE"
          | Some cs => (TextIO.print "SOME \""; print_string cs; TextIO.print "\"")
       );
       TextIO.print ", ";
       print_list_tbl (fst lst_n); (*print tablesl [[];[];[]] *)
       TextIO.print ", ";
       TextIO.print (Int.toString (snd lst_n)); (*input state*)
       TextIO.print ")")
  | Termn (fin, lst_n) =>
      (TextIO.print "termn (";
       print_action (fin);
       TextIO.print ",";    
       print_list_tbl (fst lst_n); (*print tablesl [[];[];[]] *)
       TextIO.print ", ";
       TextIO.print (Int.toString (snd lst_n)); (*input state*)
       TextIO.print ")");
’;



val res = append_prog o process_topdecs $ 
‘fun print_list_tables_lbl xs =
  let
    fun loop xs =
      case xs of
          [] => ()
        | [x] => (TextIO.print "(";
                  TextIO.print (Int.toString (fst x));
                  TextIO.print ", ";
                  print_table_label (snd x);
                  TextIO.print ")")
        | x::rest =>
            (TextIO.print "(";
             TextIO.print (Int.toString (fst x));
             TextIO.print ", ";
             print_table_label (snd x);
             TextIO.print "); \n ";
             loop rest)
  in
    TextIO.print "[";
    loop xs;
    TextIO.print "]"
          end;
’;



(***************************************)

(* EXAMPLE OF USAGE *)

(*
   
Definition policy_order_test_def:
 policy_order_test = (["x";"y";"z"]:string list)
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

                       
Definition policy_main_hol4_def:
  policy_main_hol4 =
  case sp_mk_BDD_policy policy_content_test  policy_order_test of
  | NONE => NONE
  | SOME (r,sp_edges,sp_labels) => SOME (r,
                                         ((toSortedAList sp_edges):edges),
                                         ((toSortedAList sp_labels): (((string#num list) action_expr) policy, (string#num list) action_expr) labelings) )
End





val r = translate policy_main_hol4_def;

    
val res = append_prog o process_topdecs $ 
                      ‘fun main () =
                       let
                        val args = CommandLine.arguments()
                       in
                         (case policy_main_hol4 of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>
                              (
                              TextIO.print "(" ;
                              TextIO.print (Int.toString (fst bdd));
                              (TextIO.print "n , \n");

                              TextIO.print "(" ;
                              print_tuple_list (fst (snd (bdd))) ;
                              TextIO.print "):edges , \n";

                              TextIO.print "(" ;
                              print_list_label (snd (snd (bdd))) ;
                              TextIO.print "): (((string#num list) action_expr) policy, (string#num list) action_expr) labelings";              
                              
                              TextIO.print ")" 
                              )
                               
                         )
                         end ;’
                     ; 


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                                

val _ = astToSexprLib.write_ast_to_file "test_bdd_policy.sexp" prog;

(*

cp test_bdd_policy.sexp ../bdd_cake_test



   
CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S

cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm                    

time ./test_bdd_policy.cake > bdd_policy_cakeml_export.txt

   
*)
  






 
val ins = TextIO.openIn "../bdd_cake_test/bdd_policy_cakeml_export.txt";
val content_str = TextIO.inputAll ins;
val _ = TextIO.closeIn ins;

(*open Term;*)   

val content_term =
    let
        (* Clean the string by removing newlines and backslash escapes *)
        fun clean s =
            let
                val chars = String.explode s
                fun process [] = []
                  | process (#"\\" :: #"n" :: rest) = process rest  (* remove \n *)
                  | process (c :: rest) = c :: process rest
            in
                String.implode (process chars)
            end
        
        val cleaned = clean content_str
        val parsed = Parse.Term [QUOTE cleaned]
    in
        parsed
end;






val policy_full_order = “[
  ("A",["x";"y"]);
  ("B" ,["z"])
]”;

        
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative content_term test_groupings;


    

(*
val eval_table_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ["x";"y";"z"] 1”;
*)


Definition table_content_test_def:
  table_content_test = (^gen_var_table_auto : action_table_type)
End

val r = translate table_content_test_def;

                       
Definition table_main_hol4_def:
  table_main_hol4 =
  case sp_mk_BDD_table table_content_test policy_order_test of
  | NONE => NONE
  | SOME (r,sp_edges,sp_labels) => SOME (r,
                                         ((toSortedAList sp_edges):edges),
                                         ((toSortedAList sp_labels): (action_table_type, (string#num list) action_expr) labelings) )
End


val r = translate table_main_hol4_def;

    
val res = append_prog o process_topdecs $ 
                      ‘fun main () =
                       let
                        val args = CommandLine.arguments()
                       in
                         (case table_main_hol4 of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>
                              (
                              TextIO.print "(" ;
                              TextIO.print (Int.toString (fst bdd));
                              (TextIO.print "n , \n");

                              TextIO.print "(" ;
                              print_tuple_list (fst (snd (bdd))) ;
                              TextIO.print "):edges , \n";

                              TextIO.print "(" ;
                              print_list_tables_lbl (snd (snd (bdd))) ;
                              TextIO.print "): (action_table_type, (string#num list) action_expr) labelings)"
                              )
                               
                         )
                         end ;
’; 


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                                

val _ = astToSexprLib.write_ast_to_file "test_bdd_table.sexp" prog;






(*
reset_translation   
val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 200);
*)


 
val ins = TextIO.openIn "../bdd_cake_test/outtt.txt";
val content_str = TextIO.inputAll ins;
val _ = TextIO.closeIn ins;




val content_term =
    let
        (* Clean the string by removing newlines and backslash escapes *)
        fun clean s =
            let
                val chars = String.explode s
                fun process [] = []
                  | process (#"\\" :: #"n" :: rest) = process rest  (* remove \n *)
                  | process (c :: rest) = c :: process rest
            in
                String.implode (process chars)
            end
        
        val cleaned = clean content_str
        val parsed = Parse.Term [QUOTE cleaned]
    in
        parsed
end;

*)


(*)
val _ = ml_prog_update (close_module NONE);
*)

val _ = export_theory ();
