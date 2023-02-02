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

(* This is defined as an extension to "tau" defined in p4Theory to handle type parameters *)
Datatype:
p_tau =
   p_tau_bool
   (* Note that the integer width must be a compile-time known value *)
 | p_tau_bit num_exp
 | p_tau_bot
 (* Note that structs can be type-parametrized *)
 | p_tau_xtl struct_ty ((x#p_tau) list)
 | p_tau_xl x_list
 | p_tau_err
 | p_tau_ext
 (* The string is the name of the type parameter *)
 | p_tau_par string
End

(* TODO: Rewrite this... *)
val _ = TotalDefn.tDefine "deparameterise_tau"
`(deparameterise_tau t =
  case t of
  | p_tau_bool => SOME tau_bool
  | p_tau_bit num_exp => SOME (tau_bit num_exp)
  | p_tau_bot => SOME tau_bot
  | p_tau_xtl struct_ty fields =>
   let (f_names, f_types) = UNZIP fields in
   (case deparameterise_taus f_types of
    | SOME tau_l => SOME (tau_xtl struct_ty (ZIP(f_names, tau_l)))
    | NONE => NONE
   )
(*
   (case (FOLDR ( \ field res_opt. case res_opt of
                      | SOME res =>
                       (case p4_type_from_petr4 (SND field) of
                        | SOME p4_t => SOME ((FST field, p4_t)::res)
                        | NONE => NONE)
                      | NONE => NONE) (SOME []) fields) of
   | SOME p4_fields => SOME (tau_xtl struct_ty p4_fields)
   | NONE => NONE)
*)
  | p_tau_xl x_list => SOME (tau_xl x_list)
  | p_tau_err => SOME tau_err
  | p_tau_ext => SOME tau_ext
  (* Cannot be translated to non-parameterized type *)
  | p_tau_par string => NONE) /\
(deparameterise_taus [] = SOME []) /\
(deparameterise_taus (h::t) =
  case deparameterise_tau h of
  | SOME tau =>
   (case deparameterise_taus t of
    | SOME tau_l => SOME (tau::tau_l)
    | NONE => NONE)
  | NONE => NONE)`
cheat
;

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

Definition json_to_string_wrap_def:
 json_to_string_wrap json = (FOLDL (\ str acc. str++acc) []) (json_to_string json)
End

Definition get_error_msg_def:
 get_error_msg msg json = NONE_msg (msg++(json_to_string_wrap json))
End

(* TODO: Pre-parse JSON into alternative JSON format that has enumerated type for fields instead of strings to avoid excessive string matching *)

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
     | _ => NONE_msg "petr4 format error: Top-level List did not have Array as second element")
    else NONE_msg "petr4 format error: Top level List did not have String \"program\" as first element"
   | _ => NONE_msg "petr4 format error: Empty program")
  | _ => NONE_msg "petr4 format error: JSON was not a singleton list containing an Array at top level")
 | _ => NONE_msg "output of HOL4 JSON parser did not have expected format"
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

(********************)
(* Type definitions *)

(* TODO: Expand as you encounter more types *)
Definition petr4_parse_ptype_def:
 petr4_parse_ptype tyenv json =
  case json of
  | [String "bit";
     Array [String "int";
            Object [("value",String width); ("width_signed",Null)]]] =>
   (case fromDecString width of
    | SOME w_num => SOME (p_tau_bit w_num)
    | NONE => NONE)
  | [String "error"] => SOME p_tau_err
  | [String "name";
     Array [String "BareName";
            String ty_name]] => ALOOKUP tyenv ty_name
  | _ => NONE
End

(* Version for non-parameterized types *)
Definition petr4_parse_type_def:
 petr4_parse_type tyenv json =
  case petr4_parse_ptype tyenv json of
  | SOME p_tau => deparameterise_tau p_tau
  | NONE => NONE
End

(* TODO: Merge with the above and return tuple? *)
Definition petr4_parse_type_name_def:
 petr4_parse_type_name json =
  case json of
  | [String "name";
     Array [String "BareName";
            String ty_name]] => SOME ty_name
  | _ => NONE
End

(* TODO: Brute force case expression, but does the job *)
(* TODO: Separate string comparisons into if-then-else? *)
Definition petr4_typedef_to_tyenvupdate_def:
 petr4_typedef_to_tyenvupdate tyenv json =
  case json of
  | Object
   [("annotations",Array annotations); ("name",String ty_name);
    ("typ_or_decl",
     Array
       [String "Left";
        Array type])] =>
   (case petr4_parse_ptype tyenv type of
    | SOME tau => SOME (ty_name, tau)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_parse_typedef_def:
 petr4_parse_typedef (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) json =
  case petr4_typedef_to_tyenvupdate tyenv json of
   | SOME (ty_name, tau) => SOME_msg (AUPDATE tyenv (ty_name, tau), vtymap, fmap, bltymap, gscope, pblock_map)
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

(***********************)
(* Common: expressions *)

Definition width_of_tau_def:
 width_of_tau tau =
  case tau of
  | (tau_bit w) => SOME w
  | _ => NONE
End

(* TODO: Only relevant for bitstrings, for now... *)
(* TODO: Extend tau to cover field access of structs, et.c. *)
(* TODO: vtymap uses varn_name to later use varn_star for case of function call *)
Definition exp_to_tau_def:
 exp_to_tau vtymap exp =
  case exp of
  | (e_v (v_bit (bl, n))) => SOME (tau_bit n)
  | (e_acc struct fld) =>
   (case exp_to_tau vtymap struct of
    | SOME (tau_xtl struct_ty f_t_list) =>
     (case (FIND (\ (f, t). f = fld)  f_t_list) of
      | SOME (fld, res_tau) => SOME res_tau
      | NONE => NONE
     )
    | _ => NONE)
  | (e_var (varn_name varname)) => ALOOKUP vtymap (varn_name varname) 
  | _ => NONE
End

Definition petr4_parse_value_def:
 petr4_parse_value tau_opt json =
  case json of
   | _ => NONE
End

Definition exp_to_funn_def:
 exp_to_funn exp =
  case exp of
  | (e_var (varn_name name)) => SOME (funn_name name)
  | (e_acc (e_var (varn_name ext_name)) fun_name) => SOME (funn_ext ext_name fun_name)
  | _ => NONE
End

Definition tyu_l_only_def:
(tyu_l_only [] = SOME []) /\
(tyu_l_only (h::t) =
  case h of
  | (INL a) =>
   (case tyu_l_only t of
    | SOME l => SOME (a::l)
    | NONE => NONE)
  | _ => NONE)
End

(* The image of this function is the type union of expressions (INL)
 * and natural numbers (INR) (for arbitrary-width integers).
 * Regular petr4_parse_expression is a wrapper for this which
 * rejects the INR result *)
(* Definition petr4_parse_expression_gen_def: *)
val _ = TotalDefn.tDefine "petr4_parse_expression_gen"
`(petr4_parse_expression_gen tyenv (exp, tau_opt) =
  case exp of
  (* TODO: Null can occur in case of return without value - works generally? *)
  | Null => SOME_msg (INL (e_v v_bot))
  (* Struct member/field access *)
  | Array [String "expression_member";
     Object [("expr", nested_exp);
             ("name", String mem_name)]] =>
   (case petr4_parse_expression_gen tyenv (nested_exp, NONE) of
    | SOME_msg (INL mem_nested_exp) => SOME_msg (INL (e_acc mem_nested_exp mem_name))
    | SOME_msg (INR n) => NONE_msg "cannot access field of constant"
    | NONE_msg mem_msg => NONE_msg mem_msg)
  (* Variable *)
  | Array [String "name";
     Array [String "BareName";
            String var_name]] => SOME_msg (INL (e_var (varn_name var_name)))
  (* Fixed-width (unsigned) integer *)
  | Array [String "int";
     Object [("value", String value_str);
             ("width_signed", Array [Number (Positive, width) NONE NONE; Bool F])]] =>
   (case fromDecString value_str of
    | SOME n =>
     (let bl = n2v n in
      if LENGTH bl > width then NONE_msg ("integer overflows width: "++value_str)
      else SOME_msg (INL (e_v (v_bit (fixwidth width bl, width)))))
    | NONE => NONE_msg ("could not parse string to integer: "++value_str))
  (* Arbitrary-width integer literal *)
  | Array [String "int";
     Object [("value", String value_str);
             ("width_signed", Null)]] =>
   (case tau_opt of
    | SOME tau =>
     (case width_of_tau tau of
      | SOME w =>
       (case fromDecString value_str of
        | SOME n => SOME_msg (INL (e_v (v_bit (fixwidth w (n2v n), w))))
        | NONE => NONE_msg ("could not parse string to integer: "++value_str))
      | NONE => get_error_msg "could not obtain width of expression type: " exp)
    | NONE =>
     (case fromDecString value_str of
      | SOME n => SOME_msg (INR n)
      | NONE => NONE_msg ("could not parse string to integer: "++value_str)))
  (* Binary operation *)
  | Array [String "binary_op";
     Object [("op", Array [String optype]);
             ("args", Array [op1; op2])]] =>
   (case petr4_parse_expression_gen tyenv (op1, NONE) of
    | SOME_msg res_op1 =>
     (case petr4_parse_expression_gen tyenv (op2, NONE) of
      | SOME_msg res_op2 =>
       (* TODO: Treat comparisons, bit shift+concat and regular binops differently *)
       if optype = "Eq" then
        (case (res_op1, res_op2) of
         | (INL op1_exp, INL op2_exp) => SOME_msg (INL (e_binop op1_exp binop_eq op2_exp))
         | _ => get_error_msg "type inference failed for expression: " exp)
       else if optype = "NotEq" then
        (case (res_op1, res_op2) of
         | (INL op1_exp, INL op2_exp) => SOME_msg (INL (e_binop op1_exp binop_neq op2_exp))
         | _ => get_error_msg "type inference failed for expression: " exp)
       else NONE_msg ("unknown optype: "++optype)
      | NONE_msg op2_msg => NONE_msg op2_msg)
    | NONE_msg op1_msg => NONE_msg op1_msg)
  (* Error *)
  | Array [String "error_member";
           String error_name] =>
   SOME_msg (INL (e_v (v_err error_name)))
  (* Function call *)
  | Array [String "call";
           Object [("func", func_name);
                   ("type_args", Array tyargs);
                   ("args", Array args)]] =>
   (case petr4_parse_expression_gen tyenv (func_name, NONE) of
    | SOME_msg (INL res_func_name) =>
     (case exp_to_funn res_func_name of
      | SOME res_func_name' =>
       (case petr4_parse_expressions_gen tyenv (ZIP (args, REPLICATE (LENGTH args) NONE)) of
        | SOME_msg res_args =>
         (case tyu_l_only res_args of
          | SOME res_args_inl =>
           SOME_msg (INL (e_call res_func_name' res_args_inl))
          | NONE => get_error_msg "type inference failed for function argument list: " (Array args))
        | NONE_msg func_name_msg => NONE_msg ("could not parse called function name: "++func_name_msg))
      | NONE => get_error_msg "could not parse called function name: " func_name)
    | _ => get_error_msg "unknown format of called function name: " func_name)
  | _ => get_error_msg "invalid JSON format of expression: " exp) /\
(petr4_parse_expressions_gen tyenv [] = SOME_msg []) /\
(petr4_parse_expressions_gen tyenv ((h1, h2)::t) =
 case petr4_parse_expression_gen tyenv (h1, h2) of
  | SOME_msg exp_res =>
   (case petr4_parse_expressions_gen tyenv t of
    | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
    | NONE_msg exps_msg => NONE_msg exps_msg)
  | NONE_msg exp_msg => NONE_msg ("could not parse expressions: "++exp_msg))
`
cheat
;

Definition petr4_parse_expression_def:
 petr4_parse_expression tyenv (exp, tau_opt) =
  case petr4_parse_expression_gen tyenv (exp, tau_opt) of
  | SOME_msg (INR n) => get_error_msg "type inference failed for integer constant: " exp
  | SOME_msg (INL exp) => SOME_msg exp
  | NONE_msg exp_msg => NONE_msg ("could not parse value: "++exp_msg)
End

Definition petr4_parse_expressions_def:
 (petr4_parse_expressions tyenv [] =
  SOME_msg []) /\
 (petr4_parse_expressions tyenv ((h1, h2)::t) =
  case petr4_parse_expression tyenv (h1, h2) of
   | SOME_msg exp_res =>
    (case petr4_parse_expressions tyenv t of
     | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
     | NONE_msg exps_msg => NONE_msg exps_msg)
   | NONE_msg exp_msg => NONE_msg ("could not parse expressions: "++exp_msg))
End

Definition exp_to_val_def:
 exp_to_val exp =
  case exp of
  | (e_v val) => SOME val
  | _ => NONE
End

(* This is used e.g. to parse global constants *)
Definition petr4_parse_value_def:
 petr4_parse_value tyenv (exp, tau_opt) =
  case petr4_parse_expression_gen tyenv (exp, tau_opt) of
  | SOME_msg (INR n) => SOME_msg (INR n)
  | SOME_msg (INL res_exp) =>
   (case exp_to_val res_exp of
    | SOME val => SOME_msg (INL val)
    | NONE => get_error_msg "expression could not be parsed as value: " exp)
  | NONE_msg exp_msg => NONE_msg ("could not parse value: "++exp_msg)
End

(*************)
(* Constants *)

(* TODO: Tau not used for any check? *)
(* TODO: Update compile-time constant map here *)
Definition petr4_constant_to_scopeupdate_def:
 petr4_constant_to_scopeupdate tyenv json =
  case json of
  | Object
   [("annotations", Array annotations);
    ("type", Array json_type);
    ("name", String json_name);
    ("value", json_value)] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau =>
     (* TODO: No type inference for global constants? *)
     (case petr4_parse_value tyenv (json_value, NONE) of
      | SOME_msg value => SOME_msg (varn_name json_name, value)
      | NONE_msg val_msg => NONE_msg val_msg)
    | NONE => get_error_msg "could not parse type: " (Array json_type))
  | _ => get_error_msg "invalid JSON format of constant: " json
End

Definition petr4_parse_constant_def:
 petr4_parse_constant (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) constant =
  case petr4_constant_to_scopeupdate tyenv constant of
   | SOME_msg (varn, val) => SOME_msg (tyenv, vtymap, fmap, bltymap, AUPDATE gscope (varn, val), pblock_map)
   | NONE_msg const_msg => NONE_msg ("Could not parse constant"++const_msg) (* TODO: Print constant name using nested msg *)
End

(*******************)
(* Struct + Header *)

(* TODO: This should work with nested pre-defined header types, but can you write them in-place? *)
Definition petr4_parse_struct_field_def:
 petr4_parse_struct_field tyenv struct_field =
  case struct_field of
  | Object [("annotations", Array annotations);
            ("type", Array field_type);
            ("name", String field_name)] =>
   (case petr4_parse_ptype tyenv field_type of
    | SOME tau => SOME_msg (field_name, tau)
    | NONE => NONE_msg ("Could not parse type of "++(field_name)++" in struct definition"))
  | _ => NONE_msg "Could not parse struct field"
End

(* TODO: Ensure field order is correct *)
Definition petr4_parse_struct_fields_def:
 petr4_parse_struct_fields tyenv struct_fields =
  FOLDR ( \ struct_field res_opt. case res_opt of
                     | SOME_msg res =>
                      (case petr4_parse_struct_field tyenv struct_field of
                       | SOME_msg (field_name, field_type) =>
                        SOME_msg ((field_name, field_type)::res)
                       | NONE_msg msg' => NONE_msg msg')
                     | NONE_msg msg => NONE_msg msg) (SOME_msg []) struct_fields
End

Definition petr4_struct_to_tyenvupdate_def:
 petr4_struct_to_tyenvupdate tyenv struct struct_ty =
  case struct of
  | Object
   [("annotations",Array annotations); ("name",String struct_name);
    ("fields",
     Array struct_fields)] =>
   (case petr4_parse_struct_fields tyenv struct_fields of
    | SOME_msg struct_name_tau_list => SOME_msg (struct_name, p_tau_xtl struct_ty struct_name_tau_list)
    | NONE_msg msg => NONE_msg msg)
  | _ => NONE_msg "Could not parse struct JSON object"
End

Definition petr4_parse_struct_def:
 petr4_parse_struct (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) struct struct_ty =
  case petr4_struct_to_tyenvupdate tyenv struct struct_ty of
   | SOME_msg (struct_name, tau) => SOME_msg (AUPDATE tyenv (struct_name, tau), vtymap, fmap, bltymap, gscope, pblock_map)
   | NONE_msg msg => NONE_msg ("Could not parse struct: "++msg)
End

(**********************)
(* Common: statements *)

Definition petr4_parse_args_def:
 (petr4_parse_args tyenv [] =
  SOME_msg []) /\
 (petr4_parse_args tyenv (h::t) =
  case h of
  | Array [String argtype; Object [("value", exp)]] =>
   if argtype = "Expression" then
    case petr4_parse_expression tyenv (exp, NONE) of
     | SOME_msg exp_res =>
      (case petr4_parse_args tyenv t of
       | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
       | NONE_msg exps_msg => NONE_msg exps_msg)
     | NONE_msg exp_msg => NONE_msg ("could not parse arguments: "++exp_msg)
   else NONE_msg ("unsupported argument type: "++argtype)
  | _ => get_error_msg "invalid JSON format of argument: " h)
End

Definition petr4_parse_method_call_def:
 petr4_parse_method_call (tyenv, gscope) stmt_details =
  case stmt_details of
  | [(f1, func); (* Expression: either a name or a member (in case of extern method) *)
     (f2, tyargs); (* TODO: Typically an empty list. Now thrown away *)
     (f3, Array args)] => (* Argument list: typically expressions *)
   if f1 = "func" then
    (if f2 = "type_args" then
     (if f3 = "args" then
      (case petr4_parse_expression tyenv (func, NONE) of
       | SOME_msg exp => 
        (case exp_to_funn exp of
         | SOME funn =>
          (case petr4_parse_args tyenv args of
           | SOME_msg res_args =>
            SOME_msg (stmt_ass lval_null (e_call funn res_args))
           | NONE_msg args_msg => NONE_msg ("could not parse method call: "++args_msg))
         | NONE => get_error_msg "could not parse into funn: " func)
       | NONE_msg func_msg => NONE_msg ("could not parse method call: "++func_msg))
      else NONE_msg ("invalid JSON object field of method call: "++f3))
     else NONE_msg ("invalid JSON object field of method call: "++f2))
   else NONE_msg ("invalid JSON object field of method call: "++f1)
  | _ => get_error_msg "invalid JSON format of method call: " (Object stmt_details)
End

Definition exp_to_lval_def:
 exp_to_lval exp =
  case exp of
  | (e_var (varn_name name)) => SOME (lval_varname (varn_name name))
  | (e_acc exp' field_name) =>
   (case exp_to_lval exp' of
    | SOME lval => SOME (lval_field lval field_name)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_parse_assignment_def:
 petr4_parse_assignment (tyenv, gscope) stmt_details =
  case stmt_details of
  | [(f1, lhs); (* Left-hand side: expression, should be lval *)
     (f2, rhs)] => (* Right-hand side: expression *)
   if f1 = "lhs" then
    (if f2 = "rhs" then
     (case petr4_parse_expression tyenv (lhs, NONE) of
      | SOME_msg lhs_res =>
       (case exp_to_lval lhs_res of
        | SOME lval => 
         (case petr4_parse_expression tyenv (rhs, NONE) of
          | SOME_msg rhs_res => SOME_msg (stmt_ass lval rhs_res)
          | NONE_msg rhs_msg => NONE_msg ("could not parse RHS of assignment: "++rhs_msg))
        | NONE => get_error_msg "could not parse into lval: " lhs)
      | NONE_msg lhs_msg => NONE_msg ("could not parse LHS of assignment: "++lhs_msg))
     else NONE_msg ("invalid JSON object field of assignment: "++f2))
   else NONE_msg ("invalid JSON object field of assignment: "++f1)
  | _ => get_error_msg "invalid JSON format of assignment: " (Object stmt_details)
End

Definition petr4_parse_return_def:
 petr4_parse_return (tyenv, gscope) stmt_details =
  case stmt_details of
  | [(f1, exp)] => (* Right-hand side: expression *)
   if f1 = "expr" then
     (case petr4_parse_expression tyenv (exp, NONE) of
      | SOME_msg exp_res => SOME_msg (stmt_ret exp_res)
      | NONE_msg exp_msg => NONE_msg ("could not parse return expression: "++exp_msg))
   else NONE_msg ("invalid JSON object field of return: "++f1)
  | _ => get_error_msg "invalid JSON format of return: " (Object stmt_details)
End

Definition p4_seq_stmts_def:
 (p4_seq_stmts [] = stmt_empty) /\
 (p4_seq_stmts (h::t) = FOLDL ( \ stmt stmts. stmt_seq stmt stmts) h t)
End

val _ = TotalDefn.tDefine "petr4_parse_stmt"
 `(petr4_parse_stmt (tyenv, gscope) stmt =
  case stmt of
  | Array [String stmt_name; Object stmt_details] =>
   if stmt_name = "method_call" then
    petr4_parse_method_call (tyenv, gscope) stmt_details
   else if stmt_name = "assignment" then
    SOME_msg stmt_empty
   (* Note: conditional statement is recursive *)
   else if stmt_name = "conditional" then
    case stmt_details of
    | [(f1, cond); (* Condition: expression *)
       (f2, true_case); (* True case: statement *)
       (f3, false_case)] => (* False case: statement *)
     if f1 = "cond" then
      (if f2 = "tru" then
       (if f3 = "fls" then
        (case petr4_parse_expression tyenv (cond, NONE) of
         | SOME_msg cond_res =>
          (* TODO: Will this work, since the cases are always a singleton list of a block statement? *)
          (case petr4_parse_stmt (tyenv, gscope) true_case of
           | SOME_msg true_case_res =>
            (case petr4_parse_stmt (tyenv, gscope) false_case of
             | SOME_msg false_case_res => SOME_msg (stmt_cond cond_res true_case_res false_case_res)
             | NONE_msg false_case_msg => NONE_msg ("could not parse then-case of conditional statement: "++false_case_msg))
           | NONE_msg true_case_msg => NONE_msg ("could not parse if-case of conditional statement: "++true_case_msg))
         | NONE_msg cond_msg => NONE_msg ("could not parse condition of conditional statement: "++cond_msg))
        else NONE_msg ("invalid JSON object field of conditional: "++f3))
       else NONE_msg ("invalid JSON object field of conditional: "++f2))
     else NONE_msg ("invalid JSON object field of conditional: "++f1)
    | _ => get_error_msg "invalid JSON format of conditional: " (Object stmt_details)
   else if stmt_name = "block" then
    case stmt_details of
    | [(f1, block)] =>
     if f1 = "block" then
      (case block of
       | Object [("annotations", annotations);
                 ("statements", Array stmts)] =>
        (case petr4_parse_stmts (tyenv, gscope) stmts of
         (* TODO: Must fix list of declarations for the block... *)
         | SOME_msg res_stmts => SOME_msg (stmt_block [] (p4_seq_stmts res_stmts))
         | NONE_msg stmts_msg => NONE_msg ("could not parse block: "++stmts_msg)
        )
       | _ => get_error_msg "invalid JSON format of block: " block
      )
     else NONE_msg ("invalid JSON object field of block: "++f1)
   else if stmt_name = "return" then
    petr4_parse_return (tyenv, gscope) stmt_details
   else NONE_msg ("unknown statement name: "++stmt_name)
  | Null => SOME_msg stmt_empty
  | _ => get_error_msg "invalid JSON format of statement: " stmt) /\
 (petr4_parse_stmts (tyenv, gscope) [] =
  SOME_msg []) /\
 (petr4_parse_stmts (tyenv, gscope) (h::t) =
  case petr4_parse_stmt (tyenv, gscope) h of
   | SOME_msg stmt_res =>
    (case petr4_parse_stmts (tyenv, gscope) t of
     | SOME_msg stmts_res => SOME_msg (stmt_res::stmts_res)
     | NONE_msg stmts_msg => NONE_msg stmts_msg)
   | NONE_msg stmt_msg => NONE_msg ("could not parse stmts: "++stmt_msg))`
cheat
;

Definition petr4_parse_stmts_def:
 (petr4_parse_stmts (tyenv, gscope) [] =
  SOME_msg []) /\
 (petr4_parse_stmts (tyenv, gscope) (h::t) =
  case petr4_parse_stmt (tyenv, gscope) h of
   | SOME_msg stmt_res =>
    (case petr4_parse_stmts (tyenv, gscope) t of
     | SOME_msg stmts_res => SOME_msg (stmt_res::stmts_res)
     | NONE_msg stmts_msg => NONE_msg stmts_msg)
   | NONE_msg stmt_msg => NONE_msg ("could not parse stmts: "++stmt_msg))
End

Definition p4_seq_append_stmt_def:
 p4_seq_append_stmt stmt1 stmt2 =
  case stmt1 of
  | stmt_empty => stmt2
  | _ => (stmt_seq stmt1 stmt2)
End


(*************************)
(* Functions and actions *)

(* TODO: Complete implementation *)
Definition petr4_parse_params_def:
 petr4_parse_params (tyenv, fmap, gscope) params =
  SOME_msg ([]:(string # d) list)
End

Definition petr4_function_to_fmapupdate_def:
 petr4_function_to_fmapupdate (tyenv, fmap, gscope) function =
  case function of
  | Object
   [("annotations", Array annotations);
    ("name", String f_name);
    ("params", Array params);
    ("body", Object [("annotations", Array body_annotations);
                     ("statements", Array stmts)])] =>
   (case petr4_parse_params (tyenv, fmap, gscope) params of
    | SOME_msg f_params =>
     (case petr4_parse_stmts (tyenv, fmap, gscope) stmts of
      | SOME_msg f_body => SOME_msg (f_name, (p4_seq_stmts f_body, f_params))
      | NONE_msg stmts_msg => NONE_msg stmts_msg)
    | NONE_msg params_msg => NONE_msg params_msg)
  | _ => NONE_msg "Could not parse function or action"
End

(* TODO: Decide whether to put function in global or local function map *)
Definition petr4_parse_function_def:
 petr4_parse_function (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) function =
  case petr4_function_to_fmapupdate (tyenv, fmap, gscope) function of
   | SOME_msg (f_name, (f_body, f_params)) => SOME_msg (tyenv, vtymap, AUPDATE fmap (f_name, (f_body, f_params)), bltymap, gscope, pblock_map)
   | NONE_msg msg => NONE_msg ("Could not parse struct: "++msg)
End

(***************)
(* Block types *)

Definition petr4_parse_dir_def:
 petr4_parse_dir dir =
  case dir of
  | Null => SOME_msg d_none
  | Array [String some_dir] =>
   if some_dir = "In" then SOME_msg d_in
   else if some_dir = "InOut" then SOME_msg d_inout
   else if some_dir = "Out" then SOME_msg d_out
   else NONE_msg "Could not parse direction: invalid direction name"
  | _ => NONE_msg "Could not parse direction: invalid JSON object"
End

Definition petr4_parse_type_params_def:
 (petr4_parse_type_params [] = SOME_msg []) /\
 (petr4_parse_type_params (h::t) =
   case h of
   | String typaram =>
    (case petr4_parse_type_params t of
     | SOME_msg res_msg => SOME_msg (typaram::res_msg)
     | NONE_msg err_msg => NONE_msg err_msg)
   | _ => NONE_msg "Could not parse block type parameters")
End

Definition petr4_parametrize_tyenv_def:
 petr4_parametrize_tyenv tyenv l =
  AUPDATE_LIST tyenv (MAP ( \ el. (el, p_tau_par el)) l)
End

(* Note: this uses a local, parametrized tyenv *)
Definition petr4_parse_blocktype_params_def:
 (petr4_parse_blocktype_params ptyenv [] = SOME_msg []) /\
 (petr4_parse_blocktype_params ptyenv (h::t) =
   case h of
   | Object
    [("annotations", Array annotations);
     ("direction", dir_opt);
     ("typ", Array type);
     ("variable", String p_name);
     (* TODO: Parse optional default value instead of throwing away *)
     ("opt_value", p_opt_value)] =>
    (case petr4_parse_dir dir_opt of
     | SOME_msg p_dir =>
      (case petr4_parse_ptype ptyenv type of
       | SOME p_type =>
        (case petr4_parse_blocktype_params ptyenv t of
         | SOME_msg res_msg => SOME_msg ((p_name, p_dir, p_type)::res_msg)
         | NONE_msg err_msg_params => NONE_msg err_msg_params)
       | NONE => get_error_msg "could not parse type: " (Array type))
     | NONE_msg err_msg_dir => NONE_msg err_msg_dir)
   | _ => get_error_msg "could not parse block parameters: " h)
End

(* TODO: Keep parametrized type environment in parsed block type? *)
Definition petr4_blocktype_to_bltymapupdate_def:
 petr4_blocktype_to_bltymapupdate (tyenv, fmap, bltymap, gscope) blocktype =
  case blocktype of
  | Object
   [("annotations", Array annotations);
    ("name", String blty_name);
    ("type_params", Array typarams);
    ("params", Array blparams)] =>
   (case petr4_parse_type_params typarams of
    | SOME_msg blty_typarams =>
     (case petr4_parse_blocktype_params (petr4_parametrize_tyenv tyenv blty_typarams) blparams of
      | SOME_msg blty_blparams => SOME_msg (blty_name, (blty_typarams, blty_blparams))
      | NONE_msg blparams_msg => NONE_msg (blparams_msg++" while parsing block type "++blty_name))
    | NONE_msg typarams_msg => NONE_msg (typarams_msg++" while parsing block type "++blty_name))
  | _ => NONE_msg "Invalid JSON object"
End

Definition petr4_parse_block_type_def:
 petr4_parse_block_type (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) blty blocktype_details =
  case petr4_blocktype_to_bltymapupdate (tyenv, fmap, bltymap, gscope) blocktype_details of
   | SOME_msg (blty_name, (blty_typarams, blty_blparams)) => SOME_msg (tyenv, vtymap, fmap, AUPDATE bltymap (blty_name, (blty, blty_typarams, blty_blparams)), gscope, pblock_map)
   | NONE_msg msg => NONE_msg ("Could not parse block type: "++msg)
End

(*****************)
(* Extern object *)

Definition petr4_parse_ext_object_def:
 petr4_parse_ext_object (tyenv, vtymap, fmap, bltymap, gscope, pblock_map) ext_obj =
  case ext_obj of
   | Object
    [("annotations",Array annotations);
     ("name",String ext_name);
     ("type_params", Array typarams);
     ("methods", Array methods)] =>
    SOME_msg (AUPDATE tyenv (ext_name, p_tau_ext), vtymap, fmap, bltymap, gscope, pblock_map)
   | _ => get_error_msg "Could not parse extern object: " ext_obj
End

(**********)
(* Parser *)

Definition petr4_parse_block_params_def:
 (petr4_parse_block_params ptyenv [] = SOME_msg ([], [])) /\
 (petr4_parse_block_params ptyenv (h::t) =
   case h of
   | Object
    [("annotations", Array annotations);
     ("direction", dir_opt);
     (* TODO: Type potentially needed for type inference *)
     ("typ", Array type);
     ("variable", String p_name);
     (* TODO: Parse optional default value instead of throwing away *)
     ("opt_value", p_opt_value)] =>
    (case petr4_parse_dir dir_opt of
     | SOME_msg p_dir =>
      (case petr4_parse_type ptyenv type of
       | SOME p_type =>
        (case petr4_parse_block_params ptyenv t of
         | SOME_msg (res_params_msg, res_vty_updates_msg) =>
          SOME_msg ((p_name, p_dir)::res_params_msg, (varn_name p_name, p_type)::res_vty_updates_msg)
         | NONE_msg err_msg_params => NONE_msg err_msg_params)
       | NONE => get_error_msg "could not parse type: " (Array type))
     | NONE_msg err_msg_dir => NONE_msg err_msg_dir)
   | _ => get_error_msg "could not parse block parameters: " h)
End

Definition petr4_parse_inst_def:
 petr4_parse_inst (tyenv, decl_list, inits) inst =
  case inst of
  | Object
   [("annotations", Array annotations);
    ("type", Array type);
    (* TODO: Use args as needed in constructor *)
    ("args", Array args);
    ("name", String inst_name);
    (* TODO: Make use of init field *)
    ("init", opt_init)] =>
   (case petr4_parse_type tyenv type of
    | SOME tau_ext =>
     (case petr4_parse_type_name type of
      | SOME type_name => 
       SOME_msg (decl_list++[(varn_name inst_name, tau_ext)],
                 p4_seq_append_stmt inits (stmt_ass lval_null (e_call (funn_inst type_name) [e_var (varn_name inst_name)])))
      | _ => get_error_msg "could not parse type name: " (Array type)
     )
    | SOME _ => get_error_msg "type of instantiation is not extern: " inst
    | NONE => get_error_msg "could not parse type: " (Array type)
   )
  | _ => get_error_msg "invalid JSON format of instantiation: " inst
End

Definition petr4_parse_var_def:
 petr4_parse_var (tyenv, decl_list, inits, vty_updates) var =
  case var of
  | Object
   [("annotations", Array annotations);
    ("type", Array type);
    ("name", String var_name);
    ("init", opt_init)] =>
   (case petr4_parse_type tyenv type of
    | SOME tau_var =>
     (case petr4_parse_type_name type of
      | SOME type_name =>
       (case opt_init of
        | Null =>
         SOME_msg (decl_list++[(varn_name var_name, tau_var)],inits, vty_updates++[(varn_name var_name, tau_var)])
        | _ => get_error_msg "initial values not yet supported: " opt_init)
      | _ => get_error_msg "could not parse type name: " (Array type)
     )
    | NONE => get_error_msg "could not parse type: " (Array type)
   )
  | _ => get_error_msg "invalid JSON format of variable: " var
End

Definition petr4_parse_match_kind_def:
 petr4_parse_match_kind match_kind =
  case match_kind of
  | String mk_str =>
   if mk_str = "exact"
   then SOME_msg mk_exact
   else if mk_str = "ternary"
   then SOME_msg mk_ternary
   else if mk_str = "lpm"
   then SOME_msg mk_lpm
   else NONE_msg ("unknown match kind: "++mk_str)
  | _ => get_error_msg "invalid JSON format of match kind: " match_kind
End

Definition petr4_parse_keys_def:
 (petr4_parse_keys tyenv [] = SOME_msg []) /\
 (petr4_parse_keys tyenv (h::t) =
   case h of
   | Object
    [("annotations", Array annotations);
     ("key", key);
     ("match_kind", match_kind)] =>
    (case petr4_parse_match_kind match_kind of
     | SOME_msg res_mk =>
      (case petr4_parse_expression tyenv (key, NONE) of
       | SOME_msg res_key =>
        (case petr4_parse_keys tyenv t of
         | SOME_msg res_msg => SOME_msg ((res_key, res_mk)::res_msg)
         | NONE_msg err_msg => NONE_msg err_msg)
       | NONE_msg key_msg => NONE_msg ("could not parse key: "++key_msg))
     | NONE_msg mk_msg => NONE_msg ("could not parse match kind: "++mk_msg))
   | _ => get_error_msg "invalid JSON format of key: " h)
End

(* TODO: Action argument seems to not be exported by petr4 *)
Definition petr4_parse_default_action_def:
 petr4_parse_default_action tyenv default_action =
  case default_action of
  | Object [("annotations", annotations);
            (* TODO: Don't throw this away *)
            ("const", const);
            ("name", String "default_action");
            ("value", action)] =>
   (case petr4_parse_expression tyenv (action, NONE) of
    | SOME_msg (e_var (varn_name name)) =>
     SOME_msg name
    | _ => get_error_msg "unknown format of default action name: " action)
  | _ => get_error_msg "unknown format of default action: " default_action
End

(* TODO: Note that this presupposes a default_action field *)
Definition petr4_build_table_def:
 petr4_build_table tyenv keys_obj custom_obj_opt custom_obj_opt2 =
  case petr4_parse_keys tyenv keys_obj of
  | SOME_msg keys_res =>
   (case custom_obj_opt of
    | SOME custom_obj =>
     (case custom_obj_opt2 of
      | SOME custom_obj2 =>
       (* See if first custom object is an action *)
       (case petr4_parse_default_action tyenv custom_obj of
        | SOME_msg default_action_name =>
         SOME_msg (keys_res, default_action_name)
       (* If not, second may be an action *)
        | NONE_msg def_act_msg =>
         (case petr4_parse_default_action tyenv custom_obj2 of
          | SOME_msg default_action_name2 =>
           SOME_msg (keys_res, default_action_name2)
          | NONE_msg def_act_msg2 => NONE_msg def_act_msg))
      | NONE =>
       (case petr4_parse_default_action tyenv custom_obj of
        | SOME_msg default_action_name =>
         SOME_msg (keys_res, default_action_name)
        | NONE_msg def_act_msg => NONE_msg def_act_msg))
    | NONE =>
     SOME_msg (keys_res, "NoAction"))
  | NONE_msg keys_msg => NONE_msg keys_msg
End

(* TODO: Don't throw away the "actions" field - but this requires change in Ott *)
Definition petr4_parse_properties_def:
 petr4_parse_properties tyenv props =
  case props of
  | ((Array [String "Key"; Object [("keys", Array keys_obj)]])::t) =>
   (case t of
    | ((Array [String "Actions"; actions_obj])::t') =>
     (case t' of
      | ((Array [String "Custom"; custom_obj])::t'') =>
       (case t'' of
        | [Array [String "Custom"; custom_obj2]] =>
         petr4_build_table tyenv keys_obj (SOME custom_obj) (SOME custom_obj2)
        | [] => petr4_build_table tyenv keys_obj (SOME custom_obj) NONE
        | _ => get_error_msg "unknown JSON format of table properties: " (Array props)
       )
      | [] => petr4_build_table tyenv keys_obj NONE NONE
      | _ => get_error_msg "unknown JSON format of table properties: " (Array props)
     )
    | _ => get_error_msg "unknown JSON format of table properties: " (Array props)
   )
  | _ => get_error_msg "unknown JSON format of table properties: " (Array props)
End

Definition petr4_parse_table_def:
 petr4_parse_table tyenv table =
  case table of
  | Object
   [("annotations", Array annotations);
    ("name", String tbl_name);
    ("properties", Array props)] =>
   (* Properties are: Key, Actions, Custom-"size" (optional), Custom-"default_action" (optional?) *)
   (case petr4_parse_properties tyenv props of
    | SOME_msg (keys, default_action) => SOME_msg ((tbl_name, (SND $ UNZIP keys, (default_action, []))), (tbl_name, FST $ UNZIP keys))
    | NONE_msg prop_msg => NONE_msg ("could not parse properties: "++prop_msg)
   )
  | _ => get_error_msg "invalid JSON format of table: " table
End

(* Current point of TODO: Make this also return an updated tbl_map and a block-local apply_map
 * for adding the keys to apply statements *)
Definition petr4_parse_locals_def:
 (petr4_parse_locals (tyenv, fmap, gscope) (b_func_map:b_func_map, tbl_map:tbl_map, decl_list, inits, vty_updates, apply_map) [] =
  SOME_msg (b_func_map, tbl_map, decl_list, inits, vty_updates, apply_map)) /\
 (petr4_parse_locals (tyenv, fmap, gscope) (b_func_map, tbl_map, decl_list, inits, vty_updates, apply_map) (h::t) =
  case h of
   | Array [String "Instantiation"; inst_obj] =>
    (case petr4_parse_inst (tyenv, decl_list, inits) inst_obj of
     | SOME_msg (decl_list', inits') =>
      petr4_parse_locals (tyenv, fmap, gscope) (b_func_map, tbl_map, decl_list', inits', vty_updates, apply_map) t
     | NONE_msg inst_msg => NONE_msg ("could not parse instantiation: "++inst_msg))
   | Array [String "Action"; act_obj] =>
    (case petr4_function_to_fmapupdate (tyenv, fmap, gscope) act_obj of
     | SOME_msg b_func_map_upd =>
      petr4_parse_locals (tyenv, fmap, gscope) (AUPDATE b_func_map b_func_map_upd, tbl_map, decl_list, inits, vty_updates, apply_map) t
     | NONE_msg f_msg => NONE_msg ("could not parse block-local function: "++f_msg))
   | Array [String "Variable"; var_obj] =>
    (case petr4_parse_var (tyenv, decl_list, inits, vty_updates) var_obj of
     | SOME_msg (decl_list', inits', vty_updates') =>
      petr4_parse_locals (tyenv, fmap, gscope) (b_func_map, tbl_map, decl_list', inits', vty_updates', apply_map) t
     | NONE_msg var_msg => NONE_msg ("could not parse block-local variable: "++var_msg))
   | Array [String "Table"; tab_obj] =>
    (case petr4_parse_table tyenv tab_obj of
     | SOME_msg (tbl_map_entry, apply_map_entry) =>
      petr4_parse_locals (tyenv, fmap, gscope) (b_func_map, AUPDATE tbl_map tbl_map_entry, decl_list, inits, vty_updates, AUPDATE apply_map apply_map_entry) t
     | NONE_msg tbl_msg => NONE_msg ("could not parse table: "++tbl_msg))
   | _ => get_error_msg "invalid JSON format of local: " h)
End

Definition petr4_parse_matches_def:
 (petr4_parse_matches (tyenv, g_scope) expected_tau [] = SOME_msg []) /\
 (petr4_parse_matches (tyenv, g_scope) expected_tau (h::t) =
  case h of
  | Array [String "Expression";
           Object [("expr", exp)]] =>
   (case petr4_parse_expression (tyenv, g_scope) (exp, SOME expected_tau) of
     | SOME_msg exp_res =>
      (case petr4_parse_matches (tyenv, g_scope) expected_tau t of
       | SOME_msg matches_res => SOME_msg (exp_res::matches_res)
       | NONE_msg matches_msg => NONE_msg matches_msg)
     | NONE_msg exp_msg => NONE_msg ("could not parse select match case: "++exp_msg)
   )
  | _ => get_error_msg "invalid JSON format of select case match: " h)
End

Definition petr4_parse_case_def:
 petr4_parse_case (tyenv, g_scope) expected_tau select_case =
  case select_case of
   | Object [("matches", Array match_exps);
             ("next", String state_name)] =>
    (case petr4_parse_matches (tyenv, g_scope) expected_tau match_exps of
     | SOME_msg [exp_res] =>
      (case v_of_e exp_res of
       | SOME v => SOME_msg (v, state_name)
       | NONE => get_error_msg "non-value expressions as select match cases not yet supported: " (Array match_exps))
     | SOME_msg _ => get_error_msg "lists of case matches not yet supported" (Array match_exps)
     | NONE_msg exp_msg => NONE_msg ("could not parse expression: "++exp_msg))
   | _ => get_error_msg "invalid JSON format of case: " select_case
End

Definition petr4_parse_cases_def:
 (petr4_parse_cases tyenv expected_tau [] =
  SOME_msg []) /\
 (petr4_parse_cases tyenv expected_tau (h::t) =
  case petr4_parse_case tyenv expected_tau h of
   | SOME_msg case_res =>
    (case petr4_parse_cases tyenv expected_tau t of
     | SOME_msg cases_res => SOME_msg (case_res::cases_res)
     | NONE_msg cases_msg => NONE_msg cases_msg)
   | NONE_msg case_msg => NONE_msg ("could not parse cases: "++case_msg))
End

Definition petr4_parse_trans_def:
 petr4_parse_trans (tyenv,vtymap,gscope) trans =
  case trans of
  | [String "Direct";
     Object [("next", String next_state)]] =>
   SOME_msg (stmt_trans (e_v (v_str next_state)))
  | [String "Select";
     Object [("exprs", Array exps);
             ("cases", Array cases)]] =>
    (case petr4_parse_expressions (tyenv, vtymap) (ZIP(exps, REPLICATE (LENGTH exps) NONE)) of
     (* TODO: Support multiple expressions *)
     | SOME_msg [exp_res] =>
      (* TODO: Fix this *)
      (case exp_to_tau vtymap exp_res of
       | SOME tau =>
        (case petr4_parse_cases (tyenv,vtymap,gscope) tau cases of
         | SOME_msg cases_res =>
          (* TODO: Note that reject is always default next state unless otherwise specified...
           * Hard-coded in petr4 semantics or in spec? *)
          SOME_msg (stmt_trans (e_select exp_res cases_res "reject"))
         | NONE_msg cases_msg => get_error_msg (cases_msg++" while parsing transition: ") (Array trans))
       | NONE => get_error_msg "could not parse type of " (Array exps))
     | NONE_msg exps_msg => get_error_msg (exps_msg++" while parsing transition: ") (Array trans)
     | _ => get_error_msg ("lists of expressions in select statements not supported, encountered while parsing transition: ") (Array trans))
  | _ => get_error_msg "invalid JSON format of transition: " (Array trans)
End

Definition petr4_parse_states_def:
 (petr4_parse_states (tyenv,vtymap,gscope) (pars_map:pars_map) [] =
  SOME_msg pars_map) /\
 (petr4_parse_states (tyenv,vtymap,gscope) pars_map (h::t) =
  case h of
   | Object
    [("annotations", Array annotations);
     ("name", String state_name);
     ("statements", Array stmts);
     ("transition", Array trans)] =>
    (case petr4_parse_stmts (tyenv,vtymap,gscope) stmts of
     | SOME_msg stmts_res =>
      (case petr4_parse_trans (tyenv,vtymap,gscope) trans of
       | SOME_msg trans_res =>
        petr4_parse_states (tyenv,vtymap,gscope) (AUPDATE pars_map (state_name, stmt_seq (p4_seq_stmts stmts_res) trans_res)) t
       | NONE_msg trans_msg => NONE_msg ("could not parse parser state: "++trans_msg))
     | NONE_msg stmts_msg => NONE_msg ("could not parse parser state body: "++stmts_msg))
   | _ => get_error_msg "invalid JSON format of parser state: " h)
End

Definition petr4_parse_parser_def:
 petr4_parse_parser (tyenv, vtymap, fmap, bltymap, gscope, pblock_map:pblock_map) parser =
  case parser of
   | Object
    [("annotations",Array annotations);
     ("name",String parser_name);
     ("type_params", Array typarams); (* TODO: illegal according to spec? *)
     ("params", Array params);
     ("constructor_params", Array constructor_params); (* TODO: ??? *)
     ("locals", Array locals);
     ("states", Array states)] =>
    (* TODO: Check that the parameters are a proper instantiation of the type-parametrized
     * block type parameters? *)
    (case petr4_parse_block_params tyenv params of
     | SOME_msg (pars_params, vty_updates) =>
      (case petr4_parse_locals (tyenv, fmap, gscope) ([], [], [], stmt_empty, [], []) locals of
       (* TODO: Turn p_tau in decl_list to tau *)
       | SOME_msg (b_func_map, tbl_map, decl_list, inits, vty_updates', apply_map) =>
        (case petr4_parse_states (tyenv, AUPDATE_LIST vtymap (vty_updates++vty_updates'), gscope) [] states of
         | SOME_msg pars_map =>
          SOME_msg (tyenv, vtymap, fmap, bltymap, gscope, AUPDATE pblock_map (parser_name, (pblock_regular pbl_type_parser pars_params b_func_map decl_list inits pars_map tbl_map)))
         | NONE_msg states_msg => NONE_msg ("Could not parse states: "++states_msg++" while parsing parser "++parser_name))
       | NONE_msg locals_msg => NONE_msg ("Could not parse locals: "++locals_msg++" while parsing parser "++parser_name))
     | NONE_msg blparams_msg => NONE_msg ("Could not parse block parameters: "++blparams_msg++" while parsing parser "++parser_name))
   | _ => get_error_msg "invalid JSON format of parser: " parser
End


(***********)
(* Control *)

(* TODO: Get the tables into the table map properly when parsing locals *)

Definition petr4_parse_control_def:
 petr4_parse_control (tyenv, vtymap, fmap, bltymap, gscope, pblock_map:pblock_map) control =
  case control of
   | Object
    [("annotations", Array annotations);
     ("name", String control_name);
     ("type_params", Array typarams); (* TODO: illegal according to spec? *)
     ("params", Array params);
     ("constructor_params", Array constructor_params); (* TODO: ??? *)
     ("locals", Array locals);
     ("apply", Object [("annotations", Array annotations_app);
                       ("statements", Array apply)])] =>
    (* TODO: Check that the parameters are a proper instantiation of the type-parametrized
     * block type parameters? *)
    (case petr4_parse_block_params tyenv params of
     | SOME_msg (ctrl_params, vty_updates) =>
      (case petr4_parse_locals (tyenv, fmap, gscope) ([], [], [], stmt_empty, [], []) locals of
       | SOME_msg (b_func_map, tbl_map, decl_list, inits, vty_updates', apply_map) =>
        (case petr4_parse_stmts (tyenv, AUPDATE_LIST vtymap (vty_updates++vty_updates'), gscope) apply of
         | SOME_msg res_apply =>
          (* TODO: Fix table map below *)
          SOME_msg (tyenv, vtymap, fmap, bltymap, gscope, AUPDATE pblock_map (control_name, (pblock_regular pbl_type_control ctrl_params b_func_map decl_list (stmt_seq inits (p4_seq_stmts res_apply)) ([]:pars_map) tbl_map)))
         | NONE_msg apply_msg => NONE_msg ("Could not parse apply: "++apply_msg++" while parsing control "++control_name))
       | NONE_msg locals_msg => NONE_msg ("Could not parse locals: "++locals_msg++" while parsing control "++control_name))
     | NONE_msg blparams_msg => NONE_msg ("Could not parse block parameters: "++blparams_msg++" while parsing control "++control_name))
   | _ => get_error_msg "invalid JSON format of control: " control
End

(**********************)
(* Petr4 JSON element *)
(**********************)

(* TODO: Make wrapper function for errors, so error messages can include the local variable context *)
Definition petr4_parse_element_def:
 petr4_parse_element res json =
 case json of
 | Array [String elem_name; obj] =>
  (* TODO: Give Error a separate enumeration map? *)
  if elem_name = "Error" then SOME_msg res
  (* TODO: Give MatchKind a separate enumeration map? *)
  else if elem_name = "MatchKind" then SOME_msg res
  (* WIP: Extern object types added to the type environment, since parameters to blocks
   * can be of extern type. Methods are ignored, for now... *)
  else if elem_name = "ExternObject" then petr4_parse_ext_object res obj
  (* IGNORE: Ignore, for now? *)
  else if elem_name = "ExternFunction" then SOME_msg res
  (* WIP: Add to global function map, local ones as appropriate
   *      Finish stmt parsing and param parsing *)
  else if elem_name = "Action" then petr4_parse_function res obj
  (* DONE: TypeDefs generate a type map that is checked when later elements are parsed *)
  else if elem_name = "TypeDef" then petr4_parse_typedef res obj
  (* DONE: Constants are added to the global scope.
   *      Should be added to compile-time constant map instead... *)
  else if elem_name = "Constant" then petr4_parse_constant res obj
  (* DONE: Added to type map. *)
  else if elem_name = "Struct" then petr4_parse_struct res obj struct_ty_struct
  (* DONE: Added to type map. *)
  else if elem_name = "Header" then petr4_parse_struct res obj struct_ty_header
  (* DONE: Added to new "block type map".
   * TODO: Fix default parameter values *)
  else if elem_name = "ParserType" then petr4_parse_block_type res pbl_type_parser obj
  (* DONE: Added to new "block type map".
   * TODO: Fix default parameter values *)
  else if elem_name = "ControlType" then petr4_parse_block_type res pbl_type_control obj
  (* DONE: Added to pblock_map *)
  else if elem_name = "Parser" then petr4_parse_parser res obj
  (* TODO: Added to pblock_map *)
  else if elem_name = "control" then petr4_parse_control res obj
  (* IGNORE: Ignore until multi-package support for architectures is added *)
  else if elem_name = "PackageType" then SOME_msg res
  else NONE_msg ("Unknown top-level element type: "++elem_name)
  (* TODO: ??? *)
 | _ => NONE_msg "Invalid JSON format of element"
End

Definition petr4_parse_elements_def:
 petr4_parse_elements json_list =
  FOLDL ( \ res_opt json. case res_opt of
                     | SOME_msg res => petr4_parse_element res json
                     | NONE_msg msg => NONE_msg msg) (SOME_msg ([],[],[],[],[],[])) json_list
End


(* TODO: Instead of filtering, iterate over all items and have "add_typedef", "add_constant", et.c. functions. *)
Definition p4_from_json_def:
(p4_from_json json_parse_result =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
   (* TODO: Debug here by TAKE-ing different parts of the list *)
   (case petr4_parse_elements json_list of
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

(* SIMPLE *)

val simple_in_stream = TextIO.openIn "simple_input.json";

val simple_input = TextIO.inputAll simple_in_stream;

val simple_input_tm = stringLib.fromMLstring simple_input;

val simple_lex_thm = EVAL ``lex (^simple_input_tm) ([]:token list)``;

val simple_parse_thm = EVAL ``parse (OUTL (lex (^simple_input_tm) ([]:token list))) [] T``;

val simple_parse_clean = EVAL ``p4_from_json ^(rhs $ concl simple_parse_thm)``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl simple_parse_clean;


(* VSS *)

val vss_in_stream = TextIO.openIn "vss_input.json";

val vss_input = TextIO.inputAll vss_in_stream;

val vss_input_tm = stringLib.fromMLstring vss_input;

(* Lexing: Takes ~10s *)
val vss_lex_thm = EVAL ``lex (p4_preprocess_str (^vss_input_tm)) ([]:token list)``;

(* Parsing of result of lexing: Takes ~10s. *)
val vss_parse_thm = EVAL ``parse (OUTL (lex (p4_preprocess_str (^vss_input_tm)) ([]:token list))) [] T``;

val vss_parse_clean = EVAL ``p4_from_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug1 = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl vss_parse_clean;

*)

val _ = export_theory ();
