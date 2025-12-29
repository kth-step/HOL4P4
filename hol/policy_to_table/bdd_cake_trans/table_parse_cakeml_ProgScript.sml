open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory bdd_genTheory tables_specTheory tables_spec_oldTheory;

open preamble basis ml_translatorLib ;

open fromSexpTheory;
open bdd_trans_ProgTheory;
open common_parse_cakeml_ProgTheory;



val _ = new_theory "table_parse_cakeml_Prog";



val _ = translation_extends "common_parse_cakeml_Prog"
val _ = intLib.deprecate_int();

(*This file extends the basic BDD translation for tables, where the input is parsed via cakeML *)


val res = append_prog o process_topdecs $
‘
(* Parse an atom variable *)
fun parse_atom s =
  let val s = skip_ws s in
  case s of
    #"T" :: #"r" :: #"u" :: #"e" :: rest =>
      (True_2, rest)
  | #"F" :: #"a" :: #"l" :: #"s" :: #"e" :: rest =>
      (False_2, rest)
  | #"N" :: #"o" :: #"t" :: #"t" :: #"r" :: #"u" :: #"e" :: rest =>
      (Nottrue, rest)
  | #"N" :: #"o" :: #"t" :: #"f" :: #"a" :: #"l" :: #"s" :: #"e" :: rest =>
      (Notfalse, rest)
  | #"V" :: #"a" :: #"r" :: rest =>
      let val rest = skip_ws rest
      in case rest of
        #"\"" :: _ =>
          let val (name, rest) = parse_var_name rest
          in (Var_1 name, skip_ws rest)
          end
      | _ => (True_2, rest)
      end
  | #"N" :: #"o" :: #"t" :: rest =>
      let val rest = skip_ws rest
      in case rest of
        #"\"" :: _ =>
          let val (name, rest) = parse_var_name rest
          in (Not_1 name, skip_ws rest)
          end
      | _ => (Nottrue, rest)
      end
  | #"\"" :: rest =>
      let val (name, rest) = parse_var_name (#"\"" :: rest)
      in (Var_1 name, skip_ws rest)
      end
  | _ => (True_2, s)
  end;

(* Parse a list of atoms: [Var "x"; Var "y"] *)
fun parse_atom_list s =
  let val s = skip_ws s in
  case s of
    #"[" :: rest =>
      let val s = skip_ws rest
          fun parse_list acc s =
            let val s = skip_ws s in
            case s of
              #"]" :: rest => (List.rev acc, skip_ws rest)
            | _ =>
                let val (atom, s) = parse_atom s
                    val s = skip_ws s
                in case s of
                  #";" :: rest => parse_list (atom :: acc) (skip_ws rest)
                | #"]" :: rest => (List.rev (atom :: acc), skip_ws rest)
                | _ => (List.rev (atom :: acc), s)
                end
            end
      in parse_list [] s
      end
  | _ => ([], s)
  end;

(* Parse action or state result *)
fun parse_result s =
  let val s = skip_ws s in
  case s of
    #"s" :: #"t" :: #"a" :: #"t" :: #"e" :: rest =>
      let val rest = skip_ws rest
      in case rest of
        #"(" :: rest =>
          let val rest = skip_ws rest
              val (n, rest) = parse_int rest
              val rest = skip_ws rest
          in case rest of
            #")" :: rest => (State n, skip_ws rest)
          | _ => (State n, rest)
          end
        | _ =>
          let val (n, rest) = parse_int rest
          in (State n, skip_ws rest)
          end
      end
  | #"a" :: #"c" :: #"t" :: #"i" :: #"o" :: #"n" :: rest =>
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
  end;

(* Parse a row entry: ([Var "x"; Var "y"], 0, state 3) *)
fun parse_row_entry s =
  let val s = skip_ws s in
  case s of
    #"(" :: rest =>
      let val rest = skip_ws rest
          val (atoms, rest) = parse_atom_list rest
          val rest = skip_ws rest
      in case rest of
        #"," :: rest =>
          let val rest = skip_ws rest
              val (state_in, rest) = parse_int rest
              val rest = skip_ws rest
          in case rest of
            #"," :: rest =>
              let val rest = skip_ws rest
                  val (result, rest) = parse_result rest
                  val rest = skip_ws rest
              in case rest of
                #")" :: rest => ((atoms, (state_in, result)), skip_ws rest)
              | _ => ((atoms, (state_in, result)), rest)
              end
            | _ => ((atoms, (state_in, State 0)), rest)
          end
        | _ => ((atoms, (0, State 0)), rest)
      end
  | _ => (([], (0, State 0)), s)
  end;

(* Parse a table: [([Var "x"; ...], 0, state 3); ...] *)
fun parse_table s =
  let val s = skip_ws s in
  case s of
    #"[" :: rest =>
      let val s = skip_ws rest
          fun parse_list acc s =
            let val s = skip_ws s in
            case s of
              #"]" :: rest => (List.rev acc, skip_ws rest)
            | _ =>
                let val (entry, s) = parse_row_entry s
                    val s = skip_ws s
                in case s of
                  #";" :: rest => parse_list (entry :: acc) (skip_ws rest)
                | #"]" :: rest => (List.rev (entry :: acc), skip_ws rest)
                | _ => (List.rev (entry :: acc), s)
                end
            end
      in parse_list [] s
      end
  | _ => ([], s)
  end;

(* Parse the tables list: [[...]; [...]; ...] *)
fun parse_tables_list s =
  let val s = skip_ws s in
  case s of
    #"[" :: rest =>
      let val s = skip_ws rest
          fun parse_list acc s =
            let val s = skip_ws s in
            case s of
              #"]" :: rest => (List.rev acc, skip_ws rest)
            | _ =>
                let val (tbl, s) = parse_table s
                    val s = skip_ws s
                in case s of
                  #";" :: rest => parse_list (tbl :: acc) (skip_ws rest)
                | #"]" :: rest => (List.rev (tbl :: acc), skip_ws rest)
                | _ => (List.rev (tbl :: acc), s)
                end
            end
      in parse_list [] s
      end
  | _ => ([], s)
  end;

(* Parse the entire structure: ([[...]; [...]], initial_state) *)
fun parse_tables_structure s =
  let val s = skip_ws s in
  case s of
    #"(" :: rest =>
      let val rest = skip_ws rest
          val (tbls, rest) = parse_tables_list rest
          val rest = skip_ws rest
      in case rest of
        #"," :: rest =>
          let val rest = skip_ws rest
              val (init_state, rest) = parse_int rest
              val rest = skip_ws rest
          in case rest of
            #")" :: rest => ((tbls, init_state), skip_ws rest)
          | _ => ((tbls, init_state), rest)
          end
        | _ => ((tbls, 0), rest)
      end
  | _ => (([], 0), s)
  end;

(* Pretty-print an atom *)
fun atom_to_string a =
  case a of
    True_2 => "True"
  | False_2 => "False"
  | Nottrue => "Nottrue"
  | Notfalse => "Notfalse"
  | Var_1 name => "Var(\"" ^ String.implode name ^ "\")"
  | Not_1 name => "Not(\"" ^ String.implode name ^ "\")";

(* Pretty-print a result *)
fun result_to_string r =
  case r of
    State n => "state(" ^ Int.toString n ^ ")"
  | Action (name, nums) => "action(\"" ^ String.implode name ^ "\", [" ^ int_list_to_string nums ^ "])";

(* Pretty-print a row entry *)
fun row_entry_to_string entry =
  case entry of
    (atoms, (state_in, result)) =>
      "([" ^ String.concatWith "; " (List.map atom_to_string atoms) ^ "], " ^
      Int.toString state_in ^ ", " ^ result_to_string result ^ ")";

(* Pretty-print a table *)
fun table_to_string tbl =
  "[" ^ String.concatWith "; " (List.map row_entry_to_string tbl) ^ "]";

(* Pretty-print tables list *)
fun tables_list_to_string tbls =
  "[" ^ String.concatWith "; " (List.map table_to_string tbls) ^ "]";

(* Pretty-print entire structure *)
fun tables_structure_to_string s =
  case s of
    (tbls, init_state) =>
      "(" ^ tables_list_to_string tbls ^ ", " ^ Int.toString init_state ^ ")";

(* Parse from file *)
fun parse_from_file filename =
  let
    val instream = TextIO.openIn filename
    val content = TextIO.inputAll instream
    val _ = TextIO.closeIn instream
    val chars = String.explode content
    val (result, _) = parse_tables_structure chars
  in
    result
  end;

’;






val res = append_prog o process_topdecs $
‘
fun print_bdd_table bdd =(
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
 policy_order_test = (["x";"y";"z"]:string list)
End

val r = translate policy_order_test_def;



Definition table_content_test_def:
  table_content_test = (([[([Var "is_srcPort_le_57222"; Var "is_srcPort_ge_57222"],0,state 3);
       ([Var "is_srcPort_le_57222"; Not "is_srcPort_ge_57222"],0,state 28);
       ([Not "is_srcPort_le_57222"],0,state 28)];
      [([Var "is_dstPort_le_53"; Var "is_dstPort_ge_53"],3,state 11);
       ([Var "is_dstPort_le_53"; Not "is_dstPort_ge_53"],3,state 28);
       ([Not "is_dstPort_le_53"],3,state 28); ([True],28,state 28)]],0) : action_table_type)
End

val r = translate table_content_test_def;
*)




Definition table_main_hol4_def:
  table_main_hol4 table_content_test  policy_order_test =
  mk_BDDPred_opt (table_structure) (0,[],[(0, non_termn (NONE, table_content_test))]) [] (policy_order_test) 1n
End


val r = translate table_main_hol4_def;


(*
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
          val parsed_table = parse_from_file filename1
          val parsed_order = parse_string_list_from_file filename2

          val bdd_prod = table_main_hol4 parsed_table parsed_order
          (*val _ = print "Parsed table list:\n"*)
          (*val _ = print (policy_list_to_string parsed)*)
          val _ = print "\n"
        in
          (
                              (TextIO.print "parsed \n")

                         )
        end
  end;
’;
*)


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
    val parsed_table = parse_from_file filename1
     val parsed_order = parse_string_list_from_file filename2

          val bdd_prod = table_main_hol4 parsed_table parsed_order
          (*val _ = print "Parsed policy list:\n"*)
          (*val _ = print (policy_list_to_string parsed)*)
          val _ = print "\n"
        in
          (case bdd_prod of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>  (print_bdd_table bdd; TextIO.print "\n")

                         )
        end
  end;
’;










val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs;



(* write the translation to an sexp file *)
val _ = astToSexprLib.write_ast_to_file "../bdd_cake_test/test_bdd_table.sexp" prog;




(*
bdd_cake_test$ CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_table.sexp > test_bdd_table.cake.S
bdd_cake_test$ cc test_bdd_table.cake.S basis_ffi.c -lm -o test_bdd_table.cake -lm
bdd_cake_test$ ./test_bdd_table.cake table.txt order.txt
*)


val _ = export_theory ();
