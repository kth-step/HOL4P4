open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "p4_from_json";

open stringTheory ASCIInumbersTheory;
open parse_jsonTheory;
open p4Theory;

(* For EVAL *)
open ASCIInumbersLib;

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
(p4_from_json_preamble json_parse_result =
 case json_parse_result of
 | INR (json, [], []) =>
  (* petr4: all output is a list with an array at top *)
  (case json of
  | Array json_list =>
   (* petr4: first element in this list is the string "program" *)
   (case json_list of
   | (json'::json_list') =>
    if json' = String "program"
    then
     (case json_list' of
     | [Array json_list''] => SOME_msg json_list''
     | _ => NONE_msg "petr4 format error: Array at top level not found")
    else NONE_msg "petr4 format error: List containing a String and an Array at top level did not have String \"program\" as first element"
   | _ => NONE_msg "petr4 format error: Empty program")
  | _ => NONE_msg "petr4 format error: JSON was not a singleton list containing an Array at top level")
 | _ => NONE_msg "result of JSON parser did not have expected format"
)
End

(*
("Number of program elements is: " ++ (n2s (LENGTH json_list')))
*)

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

(* TODO: Expand as you encounter more types *)
Definition petr4_parse_type_def:
 petr4_parse_type tyenv json =
  case json of
  | [String "bit";
     Array [String "int";
            Object [("value",String width); ("width_signed",Null)]]] =>
   (case fromDecString width of
    | SOME w_num => SOME (tau_bit w_num)
    | NONE => NONE)
  | [String "name";
     Array [String "BareName"; String ty_name]] => ALOOKUP tyenv ty_name
  | _ => NONE
End

(* TODO: Brute force case expression, but does the job *)
(* TODO: Separate string comparisons into if-then-else? *)
Definition petr4_typedef_to_tyenvupdate_def:
 petr4_typedef_to_tyenvupdate tyenv json =
  case json of
  | Object
   [("annotations",Array []); ("name",String ty_name);
    ("typ_or_decl",
     Array
       [String "Left";
        Array type])] =>
   (case petr4_parse_type tyenv type of
    | SOME tau => SOME (ty_name, tau)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_parse_typedef_def:
 petr4_parse_typedef (tyenv, gscope) json =
  case petr4_typedef_to_tyenvupdate tyenv json of
   | SOME (ty_name, tau) => SOME_msg (AUPDATE tyenv (ty_name, tau), gscope)
   | NONE => NONE_msg "Could not parse type definition"
End

(*
val _ = type_abbrev("scope", ``:((varn, (v # lval option)) alist)``);

varn_name of x

val _ = Hol_datatype ` 
v =  (* value *)
   v_bool of boolv (* boolean value *)
 | v_bit of bitv (* bit-string *)
 | v_str of x (* string literal *)
 | v_struct of (x#v) list (* struct *)
 | v_header of boolv => (x#v) list (* header *)
 | v_err of x (* error message *)
 | v_ext_ref of i (* extern object reference *)
 | v_bot (* no value *)
`;

Constant:

   Object
     [("annotations",Array []);
      ("type",
       Array
         [String "name";
          Array [String "BareName"; String "PortId"]]);
      ("name",String "REAL_PORT_COUNT");
      ("value",
       Array
         [String "int";
          Object
            [("value",String "8");
             ("width_signed",
              Array [Number (Positive,4) NONE NONE; Bool F])]])]
*)

(* TODO: Use tau here? *)
Definition petr4_parse_value_def:
 petr4_parse_value tau json =
  case json of
   (* Fixed-width (unsigned) value *)
   | [String "int";
      Object
       [("value", String value_str);
        ("width_signed", Array [Number (Positive, width) NONE NONE; Bool F])]
     ] =>
    (case fromDecString value_str of
     | SOME n =>
      (let bl = n2v n in
       if LENGTH bl > width then NONE
       else SOME (INL (v_bit (fixwidth width bl, width))))
     | NONE => NONE)
   (* Arbitrary-width integer literal *)
   | [String "int";
      Object
       [("value", String value_str);
        ("width_signed", Null)]
     ] =>
    (case fromDecString value_str of
     | SOME n => SOME (INR n)
     | NONE => NONE)
   | _ => NONE
End

(* TODO: Tau not used for any check? *)
(* TODO: Update compile-time constant map here *)
Definition petr4_constant_to_scopeupdate_def:
 petr4_constant_to_scopeupdate tyenv json =
  case json of
  | Object
   [("annotations", Array []);
    ("type", Array json_type);
    ("name", String json_name);
    ("value", Array json_value)] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau =>
     (case petr4_parse_value tau json_value of
      | SOME value => SOME (varn_name json_name, value)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_parse_constant_def:
 petr4_parse_constant (tyenv, gscope) constant =
  case petr4_constant_to_scopeupdate tyenv constant of
   | SOME (varn, val) => SOME_msg (tyenv, AUPDATE gscope (varn, val))
   | NONE => NONE_msg "Could not parse constant"
End

(* TODO: Make wrapper function for errors, so error messages can include the local variable context *)
Definition petr4_parse_element_def:
 petr4_parse_element res json =
 case json of
 | Array [String elem_name; obj] =>
  if elem_name = "Error" then SOME_msg res (* TODO *)
  else if elem_name = "MatchKind" then SOME_msg res (* TODO *)
  else if elem_name = "ExternObject" then SOME_msg res (* TODO *)
  else if elem_name = "ExternFunction" then SOME_msg res (* TODO *)
  else if elem_name = "Action" then SOME_msg res (* TODO *)
  else if elem_name = "TypeDef" then petr4_parse_typedef res obj
  else if elem_name = "Constant" then petr4_parse_constant res obj
  else if elem_name = "Struct" then SOME_msg res (* TODO *)
  else if elem_name = "Header" then SOME_msg res (* TODO *)
  else if elem_name = "ParserType" then SOME_msg res (* TODO *)
  else if elem_name = "ControlType" then SOME_msg res (* TODO *)
  else if elem_name = "PackageType" then SOME_msg res (* TODO *)
  else NONE_msg ("Unknown element type: "++elem_name)
 | _ => NONE_msg "Could not recognize JSON element"
End

Definition petr4_parse_elements_def:
 petr4_parse_elements json_list =
  FOLDL ( \ res_opt json. case res_opt of
                     | SOME_msg res => petr4_parse_element res json
                     | NONE_msg msg => NONE_msg msg) (SOME_msg ([],[])) json_list
End


(* TODO: Instead of filtering, iterate over all items and have "add_typedef", "add_constant", et.c. functions. *)
Definition p4_from_json_def:
(p4_from_json json_parse_result =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
  (* TODO: Here, we want to go through every element in json_list' and build all the components
   * (as far as possible) on the LHS of an architectural-level reduction step:
   *   (ab_list (partial), pblock_map, ty_map, ext_map (partially), func_map, g_scope).
   * The different types are:
   * Error
   * MatchKind

   * ExternObject
   * Action

   * TypeDef (Prototype done)
   * Constant
   * Struct
   * Header

   * ParserType
   * ControlType
   * PackageType *)
   (* TODO: Debug here by TAKE-ing different parts of the list *)
   (case petr4_parse_elements (TAKE 10 json_list) of
    | SOME_msg res =>
     SOME_msg res
    | NONE_msg msg => NONE_msg msg)
 | NONE_msg msg => NONE_msg msg
)
End

(*************)
(* DEBUGGING *)

Definition petr4_is_constant_def:
 petr4_is_constant json =
  case json of
  | Array [String "Constant"; constant] => T
  | _ => F
End

Definition petr4_filter_constants_def:
 petr4_filter_constants json_list =
  FILTER petr4_is_constant json_list
End

Definition debug_json_def:
(debug_json json_parse_result =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
  SOME_msg (petr4_filter_constants json_list)
 | NONE_msg msg => NONE_msg msg
)
End

(*********)
(* TESTS *)

(*

val simple_in_stream = TextIO.openIn "simple_input.json";

val simple_input = TextIO.inputAll simple_in_stream;

val simple_input_tm = stringLib.fromMLstring simple_input;

val simple_lex_thm = EVAL ``lex (^simple_input_tm) ([]:token list)``;

val simple_parse_thm = EVAL ``parse (OUTL (lex (^simple_input_tm) ([]:token list))) [] T``;

val simple_parse_clean = EVAL ``p4_from_json ^(rhs $ concl simple_parse_thm)``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl simple_parse_clean;



val vss_in_stream = TextIO.openIn "vss_input.json";

val vss_input = TextIO.inputAll vss_in_stream;

val vss_input_tm = stringLib.fromMLstring vss_input;

(* Takes ~10s *)
val vss_lex_thm = EVAL ``lex (p4_preprocess_str (^vss_input_tm)) ([]:token list)``;

(* Takes ~10s. *)
val vss_parse_thm = EVAL ``parse (OUTL (lex (p4_preprocess_str (^vss_input_tm)) ([]:token list))) [] T``;

val vss_parse_clean = EVAL ``p4_from_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug1 = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl vss_parse_clean;

*)

val _ = export_theory ();
