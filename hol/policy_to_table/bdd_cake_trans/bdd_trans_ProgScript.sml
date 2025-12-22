open HolKernel Parse boolLib bossLib;
open optionTheory bdd_sptrees_genTheory pairTheory bdd_genTheory tables_specTheory tables_spec_oldTheory policy_specTheory pred_specTheory;

open preamble basis ml_translatorLib ;

open miscTheory ml_translatorTheory ListProgTheory ;
open fromSexpTheory;


     
val _ = new_theory "bdd_trans_Prog";


        
val _ = translation_extends "basisProg"
val _ = intLib.deprecate_int();

(*val _ = astPP.enable_astPP ();*)

   
val r = translate update_internals_def;
val r = translate distrubute_labels_def;
val r = translate bdd_distribute_def; 
val r = translate project_labels_to_def; 

val r = translate has_parent_def;
val r = translate eliminable_def; 

val r = translate ADELKEY_def;
val r = translate merge_edges_def;
val r = translate merge_def;
val r = translate eliminate_safe_def;

val r = translate eliminable_projection_def;
val r = translate eq_vars_in_labels_def;
val r = translate mergable_projection_def;

val r = translate mergable_def;
val r = translate merge_safe_def;
    
val r = translate optimize_node_def;
val r = translate optimize_layer_def;

val r = translate project_edges_to_def;
val r = translate optimize_internals_def;

val r = translate optimize_bdd_def; 

Theorem optimize_bdd_side_cake_trans:
  optimize_bdd_side v10 v11
Proof
   cheat
QED

val _ = optimize_bdd_side_cake_trans |> update_precondition;
 

(* translation of body_of_mk part*)
val r = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate (get_leaves_list_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate getLeaves_def;

val r = translate getLabels_def;
val r = translate extract_nontermn_def;
val r = translate leaves_pred_sub_def;
val r = translate simp_pred_list_def;
val r = translate determine_termn_def;
val r = translate determine_termn_list_def;
val r = translate mk_new_labels_def;
val r = translate mk_new_edges_def;
val r = translate non_term_leaf_updt_def;

val r = translate body_of_mk_def;
val r = translate mk_BDDPred_opt_def;


(* translation of policy structure and related functions*)

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

val r = translate fv_pred_def;
val r = translate fv_policy_def;

Theorem final_policy_cake_trans:
  final_policy_side v4
Proof
  rw [fetch "-" "final_policy_side_def"] >>
  rw [fetch "-" "pre_are_fail_side_def"] >>
  rw [Once (fetch "-" "seg_side_def")] >>
  fs[min_idx_till_def] >> cheat
QED

val _ = final_policy_cake_trans |> update_precondition;

val r = ml_translatorLib.register_type ``:((pred # 'a) list, 'b) decision_structure``;
val r = translate policy_structure_def;

    
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

(*
Definition mk_BDD_policy_def:
  mk_BDD_policy (var_policy: action_policy_type ) policy_order =
  mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, var_policy))]) [] policy_order 1n
End

val r = translate mk_BDD_policy_def;
 *)                          

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




val _ = r |> hyp |> null orelse
        failwith ("Unproved pre-conditions");


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

val _ = export_theory ();


(*)        
(************* arguments passing: hardcorded arguments this *****************)

(*
Definition policy_order_test_def:
 policy_order_test = ["x"; "y"]
End

val r = translate policy_order_test_def;

Definition policy_content_test_def:
  policy_content_test =
  [
    (Var "x" , action ("fwd", [1n]));
    (Var "y" , action ("fwd", [2n]))
  ]:action_policy_type
End

val r = translate policy_content_test_def;

                       
Definition main_hol4_def:
  main_hol4 =
    mk_BDD_policy policy_content_test  policy_order_test
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

*)






(*
val _ = append_prog (process_topdecs `
  fun make_it_str bdd =
    let
      val (root, edges, labelings) = bdd
    in
      "Root: " ^ Int.toString root ^ "\n"
    end
`);
*)


        
val _ = (max_print_depth := 100)


Definition bdd_is_def:
  bdd_is =
  SOME (8,[(0,4,2);(3,4,5)]:edges,
        [(0n,
          non_termn
            (SOME "x",
             [(Var "x",action ("fwd",[1n])); (Var "y",action ("fwd",[2n]))]));
         (1,
          termn
            (action ("fwd",[1]),
             [(True,action ("fwd",[1])); (Var "y",action ("fwd",[2]))]));
         (2,
          non_termn
            (SOME "y",
             [(False,action ("fwd",[1])); (Var "y",action ("fwd",[2]))]));
         (3,
          termn
            (action ("fwd",[2]),
             [(False,action ("fwd",[1])); (True,action ("fwd",[2]))]));
         (4,
          non_termn
            (NONE,[(False,action ("fwd",[1])); (False,action ("fwd",[2]))]))])
End
    
val r = translate bdd_is_def;
        
    
(*
   

val _ = append_prog (process_topdecs `
  fun make_it_str bdd =
    let
      val (root, edges, labelings) = bdd
    in
      case root of
        SX_NUM (a) => "Root: " ^ Int.toString a ^ "\n"
      | _ => "ERRRRRRRRRRRRR"
    end
    `);
*)


val _ = append_prog (process_topdecs `
  fun edge_to_string edge_pair =
    case edge_pair of
      (from, (to1, to2)) =>
        "(" ^ Int.toString from ^ ",(" ^ Int.toString to1 ^ "," ^ Int.toString to2 ^ "))"
`);

(*
        
val _ = append_prog (process_topdecs `
              
  fun edges_to_string edges =
    case edges of
      [] => "[]"
    | ((from, (to1,  to2)), rest) => "reached edges 2"
    | ((from, (to1,  to2)), []) => "reached edges 3"
    | _ => "reached edges 4"
`);
*)


val _ = append_prog (process_topdecs `

  fun edges_to_string edges =
  case edges of       
   ((start_node, (to1,  to2)), ()) =>
     "reached edges 1" ^ (Int.toString start_node)
          
  | ((start_node, (to1, to2)), rest) =>
     (Int.toString start_node) 

  | ((),rest) => "[]"  (* Empty tuple for end *)
  | _ => "cannot find a match"

`);
        

 val _ = append_prog (process_topdecs `         
  fun make_it_str bdd =
    let
      val (root, (edges, labelings)) = bdd
    in
      case root of
        SX_NUM a => 
          "Root: " ^ Int.toString a ^ "\n" ^ edges_to_string edges  ^ "\n"

      | _ => "ERRRRRRRRRRRRR\n"
    end
`);

    
     
val res = append_prog (process_topdecs `
  fun main () =
    let
      val args = CommandLine.arguments()
    in
      case bdd_is of
        None => TextIO.print "NONE\n"
      | Some bdd => TextIO.print (make_it_str bdd_is)
    end
`);


        
 
        
val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

                 

val _ = astToSexprLib.write_ast_to_file "test_bdd.sexp" prog;





    


val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def];


val current_prog =
Decls_thm |> concl |> strip_comb |> #2 |> el 3

  
val _ = astPP.enable_astPP ();

print_term (current_prog);

val _ = astPP.disable_astPP();


                       
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


Definition policy_order_test_def:
 policy_order_test = ^policy_order
End

val r = translate policy_order_test_def;

Definition policy_content_test_def:
  policy_content_test = ^var_policy:action_policy_type
End

val r = translate policy_content_test_def;

                       
Definition main_hol4_def:
  main_hol4 =
    mk_BDD_policy policy_content_test  policy_order_test
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
*)




