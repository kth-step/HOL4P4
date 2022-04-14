open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "p4_from_json";

open stringTheory;
open parse_jsonTheory;

(* Option datatype with error message for the NONE case *)
Datatype:
 option_msg_t =
    SOME_msg 'a
  | NONE_msg string
End

(******************)
(* PRE-PROCESSING *)

(* NOTE: In the petr4 JSON output, a body can be an array, with Unparsed (a string)
 * being the first element, and [\"unused\"] (with quotation marks) presumably
 * being a singleton log message, using \" instead of ", as the second.
 * *)
(* Pre-processing will delete duplicate quotation marks and backslashes, leaving
 * only single quotation marks *)
Definition p4_preprocess_str:
(p4_preprocess_str [] = []) /\
(p4_preprocess_str (h::t) =
  if ((h = #"\"") \/ ((h = #"\\")))
  then if ((HD t = #"\"") \/ ((HD t = #"\\")))
       then (p4_preprocess_str t)
       else (h::(p4_preprocess_str t))
  else (h::(p4_preprocess_str t)))
End

(**********************)
(* HOL4 JSON TO P4OTT *)

Definition p4_from_json_preamble:
(p4_from_json_preamble json_list =
 (* petr4: all output is a list with an array at top *)
 case json_list of
 | [Array json_list] =>
  (* petr4: first element in this list is the string "program" *)
  (case json_list of
  | (json::json_list') =>
   if json = String "program"
   then SOME_msg json_list'
   else NONE_msg "petr4 format error: Singleton list containing an Array at top level did not have String \"program\" as first element"
  | _ => NONE_msg "petr4 format error: Empty program")
 | _ => NONE_msg "petr4 format error: JSON was not a singleton list containing an Array at top level"
)
End

(* LHS of the initial architectural-level reduction step:
 * actx: Contains (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
 *       ab_list: Programmable block "calls" with arguments
 *       pblock_map: Can be built from petr4 output
 *       ffblock_map: Cannot be built from petr4 output
 *       input_f: Cannot be built from petr4 output
 *       output_f: Cannot be built from petr4 output
 *       ty_map: Can be built from petr4 output
 *       ext_map: Can be partially built from petr4 output (not extern implementations)
 *       func_map: Can be built from petr4 output
 * aenv: Cannot be built from petr4 output
 * g_scope_list: First element (with the global variables) can be built from petr4.
 * arch_frame_list: Should always start as empty
 * ctrl: Cannot be built from petr4 output
 * status: Should always start as Running *)

Definition p4_from_json:
(p4_from_json json_list =
 let
  json_list' = p4_from_json_preamble json_list
  (* TODO: Here, we want to go through every element in json_list' and build all the components
   * (as far as possible) on the LHS of an architectural-level reduction step:
   *   (ab_list (partial), pblock_map, ty_map, ext_map (partially), func_map, g_scope) *)
 in
  json_list'
)
End

(*********)
(* TESTS *)

(*
val simple_in_stream = TextIO.openIn "simple_input.json";

val simple_input = TextIO.inputAll simple_in_stream;

val simple_input_tm = stringLib.fromMLstring simple_input;

val simple_lex_thm = EVAL ``lex ((^simple_input_tm), [])``;

val simple_parse_thm = EVAL ``json_of_string (^simple_input_tm)``;


val vss_in_stream = TextIO.openIn "vss_input.json";

val vss_input = TextIO.inputAll vss_in_stream;

val vss_input_tm = stringLib.fromMLstring vss_input;

(* Takes ~10-15s *)
val vss_lex_thm = EVAL ``lex (p4_preprocess_str (^vss_input_tm), [])``;

(* Takes ~3m. Also, don't print this *)
val vss_parse_thm = EVAL ``json_of_string (p4_preprocess_str (^vss_input_tm))``;

val vss_parse_thm_isSome = optionSyntax.is_some $ rhs $ concl vss_parse_thm;
*)

val _ = export_theory ();
