open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "p4_from_json";

open stringTheory;
open parse_jsonTheory;

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
