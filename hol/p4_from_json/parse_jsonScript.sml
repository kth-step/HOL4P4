open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "parse_json";

open stringTheory;

(* TODO: Cannot make object finite map... *)
Datatype ‘json_t =
             Object json_obj_t
           | Array (json_t list)
           | String string
           | Number num
           | Bool bool
           | Null ;

          json_obj_t = Map ((string # json_t) list)’;

Definition obj_empty:
 obj_empty = Map []
End

Definition obj_add:
 obj_add (k,v) (Map l) = Map ((k,v)::l)
End

Definition sym_list:
 sym_list = [#"["; #"]"; #","; #":"; #"{"; #"}"]
End

Definition is_sym:
 is_sym char =
  if MEM char sym_list
  then T
  else F
End

Datatype ‘json_token_t =
             token_id string
           | token_str string
           | token_sym char
           | token_num num’;

(*********)
(* LEXER *)

Definition lex_id:
 (lex_id [] (acc, i) token_l = SOME (((token_id (REVERSE acc))::token_l), i)) /\
 (lex_id (h::t) (acc, i) token_l =
  if (isAlphaNum h \/ (h = #"_"))
  then lex_id t ((h::acc), i+1) token_l
  else SOME (((token_id (REVERSE acc))::token_l), i))
End

Theorem lex_id_index_incr:
 !str acc i token_l token_l' i'.
 (lex_id str (acc, i) token_l = SOME (token_l', i')) ==>
 (i' >= i)
Proof
cheat
QED

Definition lex_str:
 (lex_str [] _ _ = NONE) /\
 (lex_str (h::t) (acc, i) token_l =
  if (h <> #"\"")
  then lex_str t ((h::acc), i+1) token_l
  else SOME (((token_str (REVERSE acc))::token_l), i))
End

Definition str_to_num':
 (str_to_num' [] acc _ = acc) /\
 (str_to_num' (h::t) acc i =
  str_to_num' t (acc+((ORD h - 48)*i)) (i*10))
End

Definition str_to_num:
 str_to_num str = str_to_num' (REVERSE str) 0 1
End

Definition lex_num:
 (lex_num [] _ _ = NONE) /\
 (lex_num (h::t) (acc, i) token_l =
  if isDigit h
  then lex_num t ((h::acc), i+1) token_l
  else SOME (((token_num (str_to_num acc))::token_l), i))
End

Theorem lex_num_index_incr:
 !str acc i token_l token_l' i'.
 (lex_num str (acc, i) token_l = SOME (token_l', i')) ==>
 (i' >= i)
Proof
cheat
QED

(* TODO: Also discard line break together with whitespace? *)
val lex = TotalDefn.tDefine "lex" ‘
 (lex ([], token_l) = SOME (REVERSE token_l)) /\
 (lex ((h::t), token_l) =
  let res_opt =
   if isSpace h then SOME (t, token_l)
   else if is_sym h then SOME (t, ((token_sym h)::token_l))
   else if (isAlphaNum h \/ h = #"_") then
    (case lex_id (h::t) ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP i (h::t), token_l')
     | NONE => NONE)
   else if h = #"\"" then 
    (case lex_str t ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP (i+1) t, token_l')
     | NONE => NONE)
   else if isDigit h then 
    (case lex_num (h::t) ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP i (h::t), token_l')
     | NONE => NONE)
   else NONE
  in
  case res_opt of
  | SOME res => lex res
  | NONE => NONE)’ (
WF_REL_TAC `measure (\(str, token_l). STRLEN str)` >>
REPEAT STRIP_TAC >>
Cases_on ‘isSpace h’ >> (
 fs []
) >>
Cases_on ‘is_sym h’ >> (
 fs []
) >>
Cases_on ‘isAlphaNum h’ >> (
 fs [lex_id]
) >| [
 Cases_on ‘lex_id t (STRING h "",1) token_l’ >> (
  fs []
 ) >>
 Cases_on ‘x’ >> (
  fs []
 ) >>
 IMP_RES_TAC lex_id_index_incr >>
 rw [],

 Cases_on ‘h = #"_"’ >> (
  fs [lex_id]
 ) >- (
  Cases_on ‘lex_id t ("_",1) token_l’ >> (
   fs []
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  IMP_RES_TAC lex_id_index_incr >>
  rw []
 ) >>
 Cases_on ‘h = #"\""’ >> (
  fs []
 ) >| [
  Cases_on ‘lex_str t ("",0) token_l’ >> (
   fs []
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  rw [],

  Cases_on ‘lex_num (STRING h t) ("",0) token_l’ >> (
   fs [lex_num]
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  rfs [] >>
  IMP_RES_TAC lex_num_index_incr >>
  rw []
 ]
]
);

(**********)
(* PARSER *)

(* TODO: Termination depends on pj? Restructure this? *)
val parse_jsons = TotalDefn.tDefine "parse_jsons" 
‘(parse_jsons pj jsons token_l =
 case pj token_l of
 | SOME (json, (token_sym #",")::token_l') => parse_jsons pj (json::jsons) token_l'
 | SOME (json, (token_sym #"]")::token_l') => SOME (REVERSE (json::jsons), token_l')
 | _ => NONE)’
cheat;

val [parse_json, parse_kvs, parse_kvs'] = CONJUNCTS (
TotalDefn.tDefine "parse_json_kvs" 
‘(parse_json token_l =
 case token_l of
 | ((token_str str)::token_l') => SOME (String str, token_l')
 | ((token_id "null")::token_l') => SOME (Null, token_l')
 | ((token_id "true")::token_l') => SOME (Bool T, token_l')
 | ((token_id "false")::token_l') => SOME (Bool F, token_l')
 | ((token_num n)::token_l') => SOME (Number n, token_l')
 | ((token_sym #"[")::((token_sym #"]")::token_l')) => SOME (Array [], token_l')
 | ((token_sym #"[")::token_l') =>
  (case parse_jsons parse_json [] token_l' of
   | SOME (jsons, token_l') => SOME (Array jsons, token_l')
   | _ => NONE)
 | ((token_sym #"{")::token_l') =>
  (case parse_kvs obj_empty token_l' of
   | SOME (kvs, ((token_sym #"}")::token_l')) => SOME (Object kvs, token_l')
   | _ => NONE)
 | _ => NONE) /\
(* TODO: HOL4 complains about missing parse_kvs cases
(parse_kvs acc ((token_id k)::((token_sym #":")::token_l)) =
 (case parse_json token_l of
  | SOME (json, token_l') => parse_kvs' (obj_add (k, json) acc) token_l'
  | _ => NONE)) /\
(parse_kvs acc ((token_str k)::((token_sym #":")::token_l)) =
 (case parse_json token_l of
  | SOME (json, token_l') => parse_kvs' (obj_add (k, json) acc) token_l'
  | _ => NONE)) /\
(parse_kvs acc token_l = SOME (acc, token_l)) /\
*)
(parse_kvs acc token_l =
 case token_l of
 | ((token_id k)::((token_sym #":")::token_l)) =>
  (case parse_json token_l of
   | SOME (json, token_l') => parse_kvs' (obj_add (k, json) acc) token_l'
   | _ => NONE)
 | ((token_str k)::((token_sym #":")::token_l)) =>
  (case parse_json token_l of
   | SOME (json, token_l') => parse_kvs' (obj_add (k, json) acc) token_l'
   | _ => NONE)
 | _ => SOME (acc, token_l)) /\
(parse_kvs' acc token_l =
 case token_l of
 | ((token_sym #",")::token_l') => parse_kvs acc token_l'
 | _ => SOME (acc,token_l))’
cheat);

Definition json_of_string:
(json_of_string str = 
 case lex (str, []) of
 | SOME token_l =>
  (case parse_json token_l of
   | SOME (json,nil) => SOME json
   | _ => NONE)
 | _ => NONE
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

val vss_lex_thm = EVAL ``lex ((^vss_input_tm), [])``;

val vss_parse_thm = EVAL ``json_of_string (^vss_input_tm)``;

*)

val _ = export_theory ();
