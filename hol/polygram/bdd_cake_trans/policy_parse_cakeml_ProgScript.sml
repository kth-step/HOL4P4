open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory bdd_genTheory policy_specTheory pred_specTheory;

open preamble basis ml_translatorLib ;

open fromSexpTheory;
open bdd_trans_ProgTheory;
open common_parse_cakeml_ProgTheory;


val _ = new_theory "policy_parse_cakeml_Prog";



val _ = translation_extends "common_parse_cakeml_Prog"
val _ = intLib.deprecate_int();


(*This file extends the basic BDD translation for policies,
 where the input is able to be parsed via cakeML,
   here we create one BDD that takes an two inputs
   text one for policy and one for order then outputs
   BDD in the terminal
   val _ = astToSexprLib.write_ast_to_file "../bdd_cake_test/test_bdd_policy.sexp" prog;
   *)



(* Helper function to check if character is whitespace *)
val res = append_prog o process_topdecs $
  ‘
(* Parse an action: action ("accept", [1;2]) or (action (...)) *)
fun parse_action s =
  let val s = skip_ws s
      (* Skip opening parens before action keyword *)
      fun skip_leading_parens s =
        let val s = skip_ws s in
        case s of
          #"(" :: rest => skip_leading_parens (skip_ws rest)
        | _ => s
        end
  in
  let val s = skip_leading_parens s in
  case s of
    #"a" :: #"c" :: #"t" :: #"i" :: #"o" :: #"n" :: rest =>
      let val rest = skip_ws rest
      in case rest of
        #"(" :: rest =>
          let val rest = skip_ws rest
          in case rest of
            #"\"" :: _ =>
              let val (name, rest) = parse_var_name rest
                  val rest = skip_ws rest
              in case rest of
                #"," :: rest =>
                  let val rest = skip_ws rest
                      val (nums, rest) = parse_int_list rest
                      val rest = skip_ws rest
                  in case rest of
                    #")" :: rest =>
                      let val rest = skip_ws rest
                          val rest = skip_close_parens rest
                      in (Action (name, nums), rest)
                      end
                  | _ => (Action (name, []), rest)
                  end
              | _ => (Action (name, []), rest)
              end
            | _ => (State 0, rest)
            end
        | _ => (State 0, rest)
      end
  | _ => (State 0, s)
  end
  end;
(* Main parser for predicates *)
fun parse_pred s =
  let val s = skip_ws s in
  case s of
    [] => (True_1, [])
  | #"T" :: #"r" :: #"u" :: #"e"  :: rest =>
      (True_1, rest)
  | #"F" :: #"a" :: #"l" :: #"s" :: #"e"  :: rest =>
      (False_1, rest)
  | #"V" :: #"a" :: #"r" :: rest =>
      let val rest = skip_ws rest
      in case rest of
        #"(" :: rest =>
          let val rest = skip_ws rest
              val (varname, rest) = parse_var_name rest
              val rest = skip_ws rest
          in case rest of
            #")" :: rest => (Var varname, skip_ws rest)
          | _ => (Var varname, rest)
          end
        | _ =>
          let val (varname, rest) = parse_var_name rest
          in (Var varname, skip_ws rest)
          end
      end
  | #"A" :: #"n" :: #"d" :: rest =>
      let val rest = skip_ws rest
          val (left, rest) = parse_pred rest
          val (right, rest) = parse_pred rest
      in (And left right, rest)
      end
  | #"O" :: #"r" :: rest =>
      let val rest = skip_ws rest
          val (left, rest) = parse_pred rest
          val (right, rest) = parse_pred rest
      in (Or left right, rest)
      end
  | #"N" :: #"o" :: #"t" :: rest =>
      let val rest = skip_ws rest
          val (inner, rest) = parse_pred rest
      in (Not inner, rest)
      end
  | #"I" :: #"m" :: #"p" :: #"l" :: #"i" :: #"e" :: #"s" :: rest =>
      let val rest = skip_ws rest
          val (left, rest) = parse_pred rest
          val (right, rest) = parse_pred rest
      in (Implies left right, rest)
      end
  | #"(" :: rest =>
      let val rest = skip_ws rest
          val (inner, rest) = parse_pred rest
          val rest = skip_ws rest
          fun skip_close s =
            let val s = skip_ws s in
            case s of
              #")" :: rest => skip_close (skip_ws rest)
            | _ => s
            end
      in (inner, skip_close rest)
      end
  | #"\"" :: rest =>
      let val (varname, rest) = parse_var_name (#"\"" :: rest)
      in (Var varname, skip_ws rest)
      end
  | _ => (True_1, s)
  end;
(* Parse a single policy entry: (predicate, action) *)
fun parse_policy_entry s =
  let val s = skip_ws s
  in case s of
    #"(" :: rest =>
      let val rest = skip_ws rest
          val (pred, rest) = parse_pred rest
          val rest = skip_ws rest
      in case rest of
        #"," :: rest =>
          let val rest = skip_ws rest
              val (act, rest) = parse_action rest
              val rest = skip_ws rest
              val rest = skip_close_parens rest
          in ((pred, act), rest)
          end
      | _ => ((pred, State 0), rest)
      end
  | _ => ((True_1, State 0), s)
  end;
(* Parse a list of policy entries: [(pred1, action1); (pred2, action2)] *)
fun parse_policy_list s =
  let val s = skip_ws s in
  case s of
    #"[" :: rest =>
      let val rest = skip_ws rest
          fun parse_entries acc s =
            let val s = skip_ws s in
            case s of
              #"]" :: rest => (List.rev acc, skip_ws rest)
            | _ =>
                let val (entry, s) = parse_policy_entry s
                    val s = skip_ws s
                in case s of
                  #";" :: rest =>
                    let val rest = skip_ws rest in
                    case rest of
                      #"]" :: rest => (List.rev (entry :: acc), skip_ws rest)
                    | _ => parse_entries (entry :: acc) rest
                    end
                | #"]" :: rest => (List.rev (entry :: acc), skip_ws rest)
                | _ => (List.rev (entry :: acc), s)
                end
            end
      in parse_entries [] rest
      end
  | _ => ([], s)
  end;
(* Pretty-print a pred_spec_pred *)
fun pred_to_string p =
  case p of
    True_1 => "True_1"
  | False_1 => "False_1"
  | Var chars => "Var(\"" ^ String.implode chars ^ "\")"
  | Not inner => "Not(" ^ pred_to_string inner ^ ")"
  | And left right => "And(" ^ pred_to_string left ^ ", " ^ pred_to_string right ^ ")"
  | Or left right => "Or(" ^ pred_to_string left ^ ", " ^ pred_to_string right ^ ")"
  | Implies left right => "Implies(" ^ pred_to_string left ^ ", " ^ pred_to_string right ^ ")";
(* Pretty-print an action *)
fun action_to_string act =
  case act of
    Action payload =>
      (case payload of
        (name, nums) =>
          "action(\"" ^ String.implode name ^ "\", [" ^ int_list_to_string nums ^ "])")
  | State n => "State(" ^ Int.toString n ^ ")";
(* Pretty-print a policy entry *)
fun entry_to_string entry =
  case entry of
    (pred, act) =>
      "(" ^ pred_to_string pred ^ ", " ^ action_to_string act ^ ")";
(* Pretty-print entire policy list *)
fun policy_list_to_string entries =
  case entries of
    [] => "[]"
  | _ => "[" ^ String.concatWith "; " (List.map entry_to_string entries) ^ "]";
(* Parse from file *)
fun parse_from_file filename =
  let
    val instream = TextIO.openIn filename
    val content = TextIO.inputAll instream
    val _ = TextIO.closeIn instream
    val chars = String.explode content
    val (result, _) = parse_policy_list chars
  in
    result
  end;

’;


val res = append_prog o process_topdecs $
‘
fun print_bdd_policy bdd =(
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
  );
’;



val res = append_prog o process_topdecs $
‘
fun parse_string_list s = let
  val s = skip_ws s
in
  case s of
    #"[" :: rest => let
      val rest = skip_ws rest
      fun parse_items acc s = let
        val s = skip_ws s
      in
        case s of
          #"]" :: rest => (List.rev acc, skip_ws rest)
        | #"\"" :: rest => let
            val (str_chars, rest) = parse_var_name s  (* FIXED: don't add extra quote! *)
            val s = skip_ws rest
          in
            case s of
              #";" :: rest => parse_items (str_chars :: acc) (skip_ws rest)
            | #"]" :: rest => (List.rev (str_chars :: acc), skip_ws rest)
            | _ => (List.rev (str_chars :: acc), s)
          end
        | _ => (List.rev acc, s)
      end
      val (result, rest) = parse_items [] rest
    in
      (result, rest)
    end
  | _ => ([], s)
end;

(* Parse from file - returns char list list *)
fun parse_string_list_from_file filename = let
  val instream = TextIO.openIn filename
  val content = TextIO.inputAll instream
  val _ = TextIO.closeIn instream
  val chars = String.explode content
  val (result, _) = parse_string_list chars
in
  result
end;

’;









(*
Definition policy_order_test_def:
 policy_order_test = (["x";"y"]:string list)
End

val r = translate policy_order_test_def;
*)
(*
Definition policy_content_test_def:
  policy_content_test = ([(And (Var "x") (Var "y") , action ("accept",[1;2]));
(True, action ("drop",[]));
(Or (And (Var "x") (Var "z")) (Var "y") , action ("reject",[100]));
]:action_policy_type)
End

val r = translate policy_content_test_def;
*)




Definition policy_main_hol4_def:
  policy_main_hol4 policy_content_test  policy_order_test =
  mk_BDDPred_opt (policy_structure) (0,[],[(0, non_termn (NONE, policy_content_test))]) [] (policy_order_test) 1n
End

val r = translate policy_main_hol4_def;




(* Main function *)
val res = append_prog o process_topdecs $
‘
fun main () =
  let
    val args = CommandLine.arguments ()
  in
    case args of
      [] => (print "Error: Please provide a filename\n")
    | filename1::filename2::rest =>
        let
         val parsed_policy = parse_from_file filename1
         val parsed_order = parse_string_list_from_file filename2

         val bdd_prod = policy_main_hol4 parsed_policy parsed_order
          (*val _ = print "Parsed policy list:\n"*)
          (*val _ = print (policy_list_to_string parsed_order)*)
          val _ = print "\n"
        in
          (case bdd_prod of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>
                              (print_bdd_policy bdd; TextIO.print "\n")

                         )
        end
  end;
’;


val prog =
  “SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  ” |> EVAL |> concl |> rhs;



(* write the translation to an sexp file *)
val _ = astToSexprLib.write_ast_to_file "../bdd_cake_test/test_bdd_policy.sexp" prog;




(*
val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 700);
*)

(*
bdd_cake_test$ CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S
bdd_cake_test$ cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm
bdd_cake_test$ ./test_bdd_policy.cake policy.txt order.txt
*)




val _ = export_theory ();

