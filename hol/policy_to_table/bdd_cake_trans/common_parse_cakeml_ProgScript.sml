open HolKernel Parse boolLib bossLib;
open preamble basis ml_translatorLib ;

open bdd_trans_ProgTheory;



val _ = new_theory "common_parse_cakeml_Prog";



val _ = translation_extends "bdd_trans_Prog"
val _ = intLib.deprecate_int();



val res = append_prog o process_topdecs $
‘
(* Helper function to check if character is whitespace *)
fun is_whitespace c = c = #" " orelse c = #"\n" orelse c = #"\t" orelse c = #"\r";


(* Skip whitespace and return remaining string *)
fun skip_ws s =
  case s of
    [] => []
  | c::rest => if is_whitespace c then skip_ws rest else c::rest;


(* Helper to check if character is a digit *)
fun is_digit c = (c = #"0") orelse (c = #"1") orelse (c = #"2") orelse (c = #"3")
                  orelse (c = #"4") orelse (c = #"5") orelse (c = #"6")
                  orelse (c = #"7") orelse (c = #"8") orelse (c = #"9");
(* Convert character digit to int *)
fun char_to_digit c =
  if c = #"0" then 0
  else if c = #"1" then 1
  else if c = #"2" then 2
  else if c = #"3" then 3
  else if c = #"4" then 4
  else if c = #"5" then 5
  else if c = #"6" then 6
  else if c = #"7" then 7
  else if c = #"8" then 8
  else if c = #"9" then 9
  else 0;
(* Parse a variable name (quoted) - returns char list and remaining *)
fun parse_var_name s =
  case s of
    #"\"" :: rest =>
      let fun read_until_quote acc s =
        case s of
          [] => (List.rev acc, [])
        | #"\"" :: rest => (List.rev acc, rest)
        | c :: rest => read_until_quote (c :: acc) rest
      in read_until_quote [] rest
      end
  | _ => ([], s);
(* Parse an integer - returns int and remaining *)
fun parse_int s =
  let fun read_digits acc s =
    case s of
      [] => (acc, [])
    | c::rest => if is_digit c
                  then read_digits (acc * 10 + char_to_digit c) rest
                  else (acc, c::rest)
  in
    case s of
      #"-"::rest =>
        let val (num, rest) = read_digits 0 rest
        in (~num, rest)
        end
    | _ => read_digits 0 s
  end;
(* Parse a list of integers: [1;2;3] *)
fun parse_int_list s =
  let val s = skip_ws s in
  case s of
    #"[" :: rest =>
      let val s = skip_ws rest
          fun parse_list acc s =
            let val s = skip_ws s in
            case s of
              #"]" :: rest => (List.rev acc, skip_ws rest)
            | _ =>
                let val (n, s) = parse_int s
                    val s = skip_ws s
                in case s of
                  #";" :: rest => parse_list (n :: acc) (skip_ws rest)
                | #"]" :: rest => (List.rev (n :: acc), skip_ws rest)
                | _ => (List.rev (n :: acc), s)
                end
            end
      in parse_list [] s
      end
  | _ => ([], s)
  end;
(* Helper to convert int list to string *)
fun int_list_to_string nums =
  case nums of
    [] => ""
  | n::rest =>
      case rest of
        [] => Int.toString n
      | _ => Int.toString n ^ ";" ^ int_list_to_string rest;
(* Skip closing parentheses *)
fun skip_close_parens s =
  let val s = skip_ws s in
  case s of
    #")" :: rest => skip_close_parens (skip_ws rest)
  | _ => s
  end;

(* Skip opening parentheses *)
fun skip_open_parens s =
  let val s = skip_ws s in
  case s of
    #"(" :: rest => skip_open_parens (skip_ws rest)
  | _ => s
  end;

’;


(*
val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 700);
*)


val _ = export_theory ();