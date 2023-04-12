open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "petr4_to_hol4p4";

open stringTheory ASCIInumbersTheory;
open parse_jsonTheory;
open p4Theory p4_auxTheory;

(* For EVAL *)
open ASCIInumbersLib;

(* Finds an element e obeying P in l, then returns a tuple of e and l with e removed *)
Definition FIND_EXTRACT_def:
 FIND_EXTRACT P l =
  case INDEX_FIND 0 P l of
  | SOME (j, e) => SOME (e, (TAKE j l)++(DROP (j+1) l))
  | NONE => NONE
End

(* Like FIND_EXTRACT, but returns NONE if there's more than one element obeying P *)
Definition FIND_EXTRACT_ONE_def:
 FIND_EXTRACT_ONE P l =
  case INDEX_FIND 0 P l of
  | SOME (j, e) =>
   let l' = (TAKE j l)++(DROP (j+1) l) in
   (case INDEX_FIND 0 P l' of
    | SOME (k, e') => NONE
    | NONE => SOME (e, l'))
  | NONE => NONE
End

Definition opt_pair_def:
 (opt_pair (SOME x) (SOME y) = SOME (x, y)) /\
 (opt_pair _        _        = NONE)
End

(* Option datatype with error message for the NONE case *)
Datatype:
 option_msg_t =
    SOME_msg 'a
  | NONE_msg string
End

Definition opt_add_msg_def:
 opt_add_msg msg opt =
  case opt of
  | SOME x => SOME_msg x
  | NONE => NONE_msg msg
End

Definition opt_msg_bind_def:
 (opt_msg_bind (NONE_msg msg) f = NONE_msg msg) /\
 (opt_msg_bind (SOME_msg x) f = f x)
End

(* This is defined as an extension to "tau" (defined in p4Theory) that also
 * includes type parameters *)
Datatype:
p_tau =
   p_tau_bool   (* Note that the integer width must be a compile-time known value *)
 | p_tau_bit num_exp
 | p_tau_bot
 (* Note that structs can be type-parametrized *)
 | p_tau_xtl struct_ty ((x#p_tau) list)
 | p_tau_xl x_list
 | p_tau_err
 (* The string is the name of the extern object *)
 | p_tau_ext string
 (* The string is the name of the package *)
 | p_tau_pkg string
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
  | p_tau_xl x_list => SOME (tau_xl x_list)
  | p_tau_err => SOME tau_err
  | p_tau_ext ext_name => SOME tau_ext
  (* Cannot be translated to non-parameterized type *)
  | p_tau_par param_name => NONE) /\
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

(* Note: this assigns the extern object name "" to all extern types *)
val _ = TotalDefn.tDefine "parameterise_tau"
`(parameterise_tau t =
  case t of
  | tau_bool => p_tau_bool
  | tau_bit num_exp => (p_tau_bit num_exp)
  | tau_bot => p_tau_bot
  | tau_xtl struct_ty fields =>
   let (f_names, f_types) = UNZIP fields in
    (p_tau_xtl struct_ty (ZIP(f_names, parameterise_taus f_types)))
  | tau_xl x_list => (p_tau_xl x_list)
  | tau_err => p_tau_err
  | tau_ext => p_tau_ext "") /\
(parameterise_taus [] = []) /\
(parameterise_taus (h::t) = ((parameterise_tau h)::(parameterise_taus t)))`
cheat
;

(******************)
(* PRE-PROCESSING *)

(* NOTE: This deals with "\"unused\"" in the situation where "" can also occur *)
(* TODO: Normally this would require a length of t check, but we know it will always
 * end in ]] due to petr4 format *)
Definition p4_preprocess_str_def:
(p4_preprocess_str [] = []) /\
(p4_preprocess_str (h::t) =
 if (h = #"\"")
 then if ((EL 1 t = #"\\") /\ ((EL 2 t = #"\"")))
      then (p4_preprocess_str t)
      else (h::(p4_preprocess_str t))
 else if (h = #"\\")
 then if ((EL 1 t = #"\"") /\ ((EL 2 t = #"\"")))
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

Definition json_dest_str_def:
 json_dest_str json =
  case json of
  | String s => SOME s
  | _ => NONE
End

Definition json_dest_obj_def:
 json_dest_obj json =
  case json of
  | Object obj => SOME obj
  | _ => NONE
End

Definition json_dest_arr_def:
 json_dest_arr json =
  case json of
  | Array arr => SOME arr
  | _ => NONE
End

(* TODO: Rename this and all parse_ functions to json_parse? *)
Definition json_parse_obj'_def:
 (json_parse_obj' [] [] = SOME []) /\
 (json_parse_obj' [] _  = NONE) /\
 (json_parse_obj' _  [] = NONE) /\
 (json_parse_obj' (h2::t2) ((k, v)::t) =
  if k = h2
  then
   (case json_parse_obj' t2 t of
    | SOME vl => SOME (v::vl)
    | NONE => NONE)
  else NONE)
End

(* Returns a list of the JSON elements that are the
 * values of the members of json iff the keys match
 * the provided list of strings *)
Definition json_parse_obj_def:
 json_parse_obj fields json =
  OPTION_BIND (json_dest_obj json) (json_parse_obj' fields) 
End

Definition json_parse_arr'_def:
 (json_parse_arr' _  _ [] = NONE) /\
 (json_parse_arr' name f (h::[t]) =
  OPTION_BIND
   (json_dest_str h)
   (\s. if s = name then f t else NONE))
End

(* Returns the JSON that is the second element of json iff
 * the first elements is a String that matches the provided string.
 * Note that this is not the general format of a JSON array, but rather
 * a specific pattern found in petr4 JSON exports. *)
Definition json_parse_arr_def:
 json_parse_arr name f json =
  OPTION_BIND (json_dest_arr json) (json_parse_arr' name f)
End

Definition json_parse_arr_list'_def:
 (json_parse_arr_list' _ [] = NONE) /\
 (json_parse_arr_list' name_f_l (h::t) =
  OPTION_BIND
   (json_dest_str h)
   (\s.
    (case INDEX_FIND 0 (\name_f. (FST name_f) = s) name_f_l of
     | SOME (i, name_f) =>
      (* t can be empty if we're dealing with an error *)
      (case t of
       | [] =>
        (SND name_f) Null
       | [t'] =>
        (SND name_f) t'
       | _ => NONE)
     | _ => NONE)))
End

(* Parses the JSON element using one of the options in name_f_l, depending
 * on the String value, which has to be the first element of the list *)
Definition json_parse_arr_list_def:
 json_parse_arr_list name_f_l json =
  case json of 
  | Array arr_elems => json_parse_arr_list' name_f_l arr_elems
  | _ => NONE
End

(* TODO: Pre-parse JSON into alternative JSON format that has enumerated type for fields instead of strings to avoid excessive string matching? *)

(**********************)
(* HOL4 JSON TO P4OTT *)

(* TODO: Fix this... *)
Definition p4_from_json_preamble:
 p4_from_json_preamble json_parse_result =
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

val _ = type_abbrev("tyenv", ``:(string, p_tau) alist``);
val _ = type_abbrev("enummap", ``:num # (string # (string, v) alist) list``);
val _ = type_abbrev("ftymap", ``:(funn # (p_tau list, tau) alist)``);

Datatype:
 vss_pkg_t =
  vss_pkg_VSS
End

Datatype:
 ebpf_pkg_t =
  ebpf_pkg_ebpfFilter
End

Datatype:
 arch_t =
    arch_vss (vss_pkg_t option)
  | arch_ebpf (ebpf_pkg_t option)
End


(********************)
(* Type definitions *)

Definition petr4_parse_width_def:
 petr4_parse_width json_list =
  case json_list of
  | [String width; Null] => 
   (case fromDecString width of
    | SOME w_num => SOME (p_tau_bit w_num)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_deparse_name_def:
 petr4_deparse_name name_str =
  Object [("tags",Array []); ("string",String name_str)]
End

Definition petr4_parse_name_def:
 petr4_parse_name name_obj =
  case json_parse_obj ["tags"; "string"] name_obj of
   | SOME [tags; name] =>
    json_dest_str name
   | _ => NONE
End

Definition petr4_parse_names_def:
 (petr4_parse_names [] = SOME []) /\
 (petr4_parse_names (h::t) =
   case petr4_parse_name h of
   | SOME res_hd =>
    (case petr4_parse_names t of
     | SOME res_tl => SOME (res_hd::res_tl)
     | NONE => NONE)
   | _ => NONE)
End

Definition petr4_parse_bare_name_def:
 petr4_parse_bare_name bname =
  case json_parse_arr "BareName" SOME bname of
   | SOME bname_obj =>
    (case json_parse_obj ["tags"; "name"] bname_obj of
     | SOME [tags; name] => petr4_parse_name name
     | _ => NONE)
   | _ => NONE
End

(* Parses a named type *)
(* TODO: This is currently used also to parse variable names... *)
Definition petr4_parse_tyname_def:
 petr4_parse_tyname json =
  case json_parse_obj ["tags"; "name"] json of
  | SOME [tags; name] =>
   petr4_parse_bare_name name
  | _ => NONE
End

(* Parses a type to a string, should return NONE if type is not a named type *)
Definition petr4_parse_type_name_def:
 petr4_parse_type_name json =
  OPTION_BIND
   (json_parse_arr "name" SOME json)
   petr4_parse_tyname
End

(* TODO: Expand as you encounter more types *)
(* If type specialisation is ignored via "ignore_tyspec", type-specialised types
 * will be treated as their base type: this will result in p_tau_par.
 * This is used e.g. when parsing package types, when only the base type of the
 * parameter is relevant. *)
Definition petr4_parse_ptype_def:
 petr4_parse_ptype ignore_tyspec tyenv json =
  let 
   arr_optional =
    if ignore_tyspec
    then [("specialized", \json'.
                           (case json_parse_obj ["tags"; "base"; "args"] json' of
                            | SOME [tags; base; args] =>
                             OPTION_BIND (petr4_parse_type_name base)
                                  (\name. SOME (p_tau_par name))
                            | _ => NONE))]
    else []
  in
  json_parse_arr_list
   ([("bit", \json'.
              (case json_parse_obj ["tags"; "expr"] json' of
               | SOME [tags; expr] =>
                (case json_parse_arr "int" SOME expr of
                 | SOME int_obj =>
                  (case json_parse_obj ["tags"; "x"] int_obj of
                   | SOME [int_tags; x_obj] =>
                    (case json_parse_obj ["tags"; "value"; "width_signed"] x_obj of
                     | SOME [x_tags; value; width] =>
                      petr4_parse_width [value; width]
                     | _ => NONE)
                   | _ => NONE)
                 | _ => NONE)
               | _ => NONE));
     ("bool", \json'. SOME p_tau_bool);
     ("error", \json'. SOME p_tau_err);
     ("name", \json'. OPTION_BIND (petr4_parse_tyname json')
                                  (\name. case ALOOKUP tyenv name of
                                   | SOME p_tau => SOME p_tau
                                   | NONE => SOME (p_tau_par name)));
     (* Note. It's OK to map the string type to p_tau_bot, since we never want to
      * do type inference in expressions of this type. *)
     ("string", \json'. SOME p_tau_bot)]++arr_optional) json
End

(* Version for non-parameterized types *)
Definition petr4_parse_type_def:
 petr4_parse_type tyenv json =
  case petr4_parse_ptype F tyenv json of
  | SOME p_tau => deparameterise_tau p_tau
  | NONE => NONE
End

(* TODO: Avoid explicit case matching on list possible? *)
Definition petr4_typedef_to_tyenvupdate_def:
 petr4_typedef_to_tyenvupdate tyenv json =
  case json_parse_obj ["tags"; "annotations"; "name"; "typ_or_decl"] json of
  | SOME [tags; annot; ty_name; typ_or_decl] =>
   opt_pair
    (petr4_parse_name ty_name)
    (OPTION_BIND
     (json_parse_arr "Left" SOME typ_or_decl)
     (petr4_parse_ptype F tyenv))
  | _ => NONE
End

Definition petr4_parse_typedef_def:
 petr4_parse_typedef tyenv json =
  case petr4_typedef_to_tyenvupdate tyenv json of
   | SOME (ty_name, tau) =>
    SOME_msg (AUPDATE tyenv (ty_name, tau))
   | NONE => NONE_msg "Could not parse type definition"
End

(*********************)
(* Enumeration types *)

Definition COUNT_LIST_interval_def:
 COUNT_LIST_interval n m =
  DROP n (COUNT_LIST (n+m))
End

Definition get_32bitv_def:
 get_32bitv n =
  v_bit (fixwidth 32 (n2v n), 32)
End

(* Note that currently, if any error or match_kind enumeration members are
 * re-declared, they get a new number *)
(* TODO: Fix code duplication *)
Definition petr4_enum_to_enummapupdates_def:
 petr4_enum_to_enummapupdates enummap name members =
  case petr4_parse_name name of
  | SOME enum_name => 
   if (enum_name = "error") \/ (enum_name = "match_kind")
   then
    (case petr4_parse_names members of
     | SOME enum_members => 
      (case ALOOKUP (SND enummap) enum_name of
       | SOME enum_mem_map =>
        SOME (FST enummap + LENGTH enum_members,
              AUPDATE (SND enummap) (enum_name,
                AUPDATE_LIST enum_mem_map (ZIP (enum_members,
                                                MAP get_32bitv (COUNT_LIST_interval (FST enummap) (LENGTH enum_members))))))
       | NONE =>
        SOME (FST enummap + LENGTH enum_members,
              AUPDATE (SND enummap) (enum_name,
                AUPDATE_LIST [] (ZIP (enum_members,
                                      MAP get_32bitv (COUNT_LIST_interval (FST enummap) (LENGTH enum_members)))))))
     | NONE => NONE)
   else if (ALOOKUP (SND enummap) enum_name = NONE)
   then
    (case petr4_parse_names members of
     | SOME enum_members =>
      SOME (FST enummap + LENGTH enum_members,
              AUPDATE (SND enummap) (enum_name,
                AUPDATE_LIST [] (ZIP (enum_members,
                                      MAP get_32bitv (COUNT_LIST_interval (FST enummap) (LENGTH enum_members))))))
     | NONE => NONE)
   else NONE
  | NONE => NONE
End

(* Note: enummap updated directly here *)
Definition petr4_parse_enum_def:
 petr4_parse_enum enummap json =
  case json_parse_obj ["tags"; "annotations"; "name"; "members"] json of
  | SOME [tags; annot; name; Array members] =>
   (case petr4_enum_to_enummapupdates enummap name members of
    | SOME enummap' =>
     SOME_msg enummap'
    | NONE => get_error_msg "Could not parse enumeration type: " json)
  | _ => get_error_msg "Unknown JSON format of enumeration type: " json
End

Definition petr4_parse_error_def:
 petr4_parse_error enummap json =
  case json_parse_obj ["tags"; "members"] json of
  | SOME [tags; Array members] =>
   (case petr4_enum_to_enummapupdates enummap (petr4_deparse_name "error") members of
    | SOME enummap' =>
     SOME_msg enummap'
    | NONE => get_error_msg "Could not parse error type: " json)
  | _ => get_error_msg "Unknown JSON format of error type: " json
End

Definition petr4_parse_match_kind_typedef_def:
 petr4_parse_match_kind_typedef enummap json =
  case json_parse_obj ["tags"; "members"] json of
  | SOME [tags; Array members] =>
   (case petr4_enum_to_enummapupdates enummap (petr4_deparse_name "match_kind") members of
    | SOME enummap' =>
     SOME_msg enummap'
    | NONE => get_error_msg "Could not parse match kind type: " json)
  | _ => get_error_msg "Unknown JSON format of match kind type: " json
End


(***********************)
(* Common: expressions *)

Definition width_of_tau_def:
 width_of_tau tau =
  case tau of
  | (tau_bit w) => SOME w
  | _ => NONE
End

Definition width_of_p_tau_def:
 width_of_p_tau p_tau =
  case p_tau of
  | (p_tau_bit w) => SOME w
  | _ => NONE
End

(* TODO: Only relevant for bitstrings, for now... *)
(* TODO: Extend tau to cover field access of structs, et.c. *)
(* TODO: vtymap uses varn_name to later use varn_star for case of function call *)
Definition exp_to_p_tau_def:
 exp_to_p_tau vtymap exp =
  case exp of
  | (e_v (v_bit (bl, n))) => SOME (p_tau_bit n)
  | (e_acc struct fld) =>
   (case exp_to_p_tau vtymap struct of
    | SOME (p_tau_xtl struct_ty f_t_list) =>
     (case (FIND (\ (f, t). f = fld)  f_t_list) of
      | SOME (fld, res_tau) => SOME res_tau
      | NONE => NONE)
    | _ => NONE)
  | (e_var (varn_name varname)) => ALOOKUP vtymap (varn_name varname) 
  | _ => NONE
End

Definition exp_to_funn_def:
 exp_to_funn vtymap exp =
  case exp of
  (* Regular function call *)
  | (e_var (varn_name name)) => SOME (SOME (funn_name name), NONE)
  (* Extern method call/isValid *)
  | (e_acc obj fun_name) =>
     (* TODO: This is a hack, making exceptions for "isValid" and "apply"...
      *       Need to check type of obj to see what methods exist *)
   (if fun_name = "isValid" then
     SOME (SOME (funn_ext "header" "isValid"), SOME obj)
    else if fun_name = "apply" then
     (* Apply is a statement, no function name needed *)
     SOME (NONE, SOME obj)
    else
    (case obj of
     (* TODO: Note that "ext_name" is here the name of the specific object, not the object type.
      * In HOL4P4, this should be the extern object type and the object itself be the first
      * argument to the function. *)
     | (e_var (varn_name ext_name)) =>
      (case ALOOKUP vtymap (varn_name ext_name) of
       | SOME (p_tau_ext ext_tyname) =>
        SOME (SOME (funn_ext ext_tyname fun_name), SOME obj)
       | _ => NONE)
     | _ => NONE))
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

Definition petr4_unop_lookup_def:
 petr4_unop_lookup unop_str = 
  ALOOKUP [("Not", unop_neg);
           ("BitNot", unop_compl);
           ("UMinus", unop_neg_signed)] unop_str
End

(* TODO: Saturating addition/subtraction, ++? *)
Definition petr4_binop_lookup_def:
 petr4_binop_lookup binop_str = 
  ALOOKUP [("Plus", binop_add);
           ("Minus", binop_sub);
           ("Mul", binop_mul);
           ("Div", binop_div);
           ("Mod", binop_mod);
           ("Shl", binop_shl);
           ("Shr", binop_shr);
           ("Le", binop_le);
           ("Ge", binop_ge);
           ("Lt", binop_lt);
           ("Gt", binop_gt);
           ("Eq", binop_eq);
           ("NotEq", binop_neq);
           ("BitAnd", binop_and);
           ("BitXor", binop_xor);
           ("BitOr", binop_or);
           ("And", binop_bin_and);
           ("Or", binop_bin_or)] binop_str
End

(* The image of this function is the type union of expressions (INL)
 * and natural numbers (INR) (for arbitrary-width integers).
 * Regular petr4_parse_expression is a wrapper for this which
 * rejects the INR result *)
(* Definition petr4_parse_expression_gen_def: *)
(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
val _ = TotalDefn.tDefine "petr4_parse_expression_gen"
`(petr4_parse_expression_gen (tyenv, enummap, vtymap) (exp, p_tau_opt) =
  case exp of
  (* TODO: Null can occur in case of return without value - works generally? *)
  | Null => SOME_msg (INL (e_v v_bot))
  (* True and false *)
  | Array [String "true";
     Object [("tags", tags)]] =>
   SOME_msg (INL (e_v (v_bool T)))
  | Array [String "false";
     Object [("tags", tags)]] =>
   SOME_msg (INL (e_v (v_bool F)))
  (* Struct member/field access *)
  | Array [String "expression_member";
     Object [("tags", tags);
             ("expr", nested_exp);
             ("name", name)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap) (nested_exp, NONE) of
    | SOME_msg (INL mem_nested_exp) =>
     (case petr4_parse_name name of
      | SOME mem_name =>
       SOME_msg (INL (e_acc mem_nested_exp mem_name))
      | NONE => get_error_msg "could not parse name: " name)
    | SOME_msg (INR n) => NONE_msg "cannot access field of constant"
    | NONE_msg mem_msg => NONE_msg mem_msg)
  (* Variable *)
  | Array [String "name";
           name] =>
   (case petr4_parse_tyname name of
    | SOME var_name =>
     SOME_msg (INL (e_var (varn_name var_name)))
    | NONE => get_error_msg "could not parse name: " name)
  (* Arbitrary-width integer literal + fixed-width (unsigned) integer *)
  | Array [String "int";
     Object [("tags", tags);
             ("x", x)]] =>
   (case x of
    | Object [("tags", tags2);
              ("value", String value_str);
              ("width_signed", width_signed)] =>
     (case width_signed of
      | Null =>
       (case p_tau_opt of
        | SOME p_tau =>
         (case width_of_p_tau p_tau of
          | SOME w =>
           (case fromDecString value_str of
            | SOME n => SOME_msg (INL (e_v (v_bit (fixwidth w (n2v n), w))))
            | NONE => NONE_msg ("could not parse string to integer: "++value_str))
          | NONE => get_error_msg "could not obtain width of expression type: " exp)
        | NONE =>
         (case fromDecString value_str of
          | SOME n => SOME_msg (INR n)
          | NONE => NONE_msg ("could not parse string to integer: "++value_str)))
      | Array [Number (Positive, width) NONE NONE; Bool F] =>
       (case fromDecString value_str of
        | SOME n =>
         (let bl = n2v n in
          if LENGTH bl > width then NONE_msg ("integer overflows width: "++value_str)
          else SOME_msg (INL (e_v (v_bit (fixwidth width bl, width)))))
        | NONE => NONE_msg ("could not parse string to integer: "++value_str))
      | _ => get_error_msg "unsupported integer type: " width_signed)
    | _ => get_error_msg "could not obtain value and width of integer literal: " x)
  (* Unary operation *)
  | Array [String "unary_op";
     Object [("tags", tags);
             ("op", Array [String optype; op_tags]);
             ("arg", op)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap) (op, NONE) of
    | SOME_msg res_op =>
     (* TODO: Treat comparisons, bit shift+concat and regular binops differently *)
     (case petr4_unop_lookup optype of
      | SOME unop =>
       (case res_op of
        | INL op_exp =>
         SOME_msg (INL (e_unop unop op_exp))
        | INR op_const =>
         (* TODO: Infer type directly from tau_opt *)
         get_error_msg "type inference unsupported for unops: " exp)
      | NONE => NONE_msg ("unknown optype: "++optype))
    | NONE_msg op_msg => NONE_msg op_msg)
  (* Binary operation *)
  | Array [String "binary_op";
     Object [("tags", tags);
             ("op", Array [String optype; op_tags]);
             ("args", Array [op1; op2])]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap) (op1, NONE) of
    | SOME_msg res_op1 =>
     (case petr4_parse_expression_gen (tyenv, enummap, vtymap) (op2, NONE) of
      | SOME_msg res_op2 =>
       (* TODO: Treat comparisons, bit shift+concat and regular binops differently *)
       (case petr4_binop_lookup optype of
        | SOME binop =>
         (case (res_op1, res_op2) of
          | (INL op1_exp, INL op2_exp) => SOME_msg (INL (e_binop op1_exp binop op2_exp))
          | (INL op1_exp, INR op2_const) =>
           (case exp_to_p_tau vtymap op1_exp of
            | SOME (p_tau_bit n) =>
             SOME_msg (INL (e_binop op1_exp binop (e_v (v_bit (fixwidth n (n2v op2_const), n)))))
            | SOME _ => get_error_msg "non-bitstring type inference unsupported for expression: " exp
            | NONE => get_error_msg "type inference failed for expression: " exp)
          | (INR op1_const, INL op2_exp) =>
           (case exp_to_p_tau vtymap op2_exp of
            | SOME (p_tau_bit n) =>
             SOME_msg (INL (e_binop (e_v (v_bit (fixwidth n (n2v op1_const), n))) binop op2_exp))
            | SOME _ => get_error_msg "non-bitstring type inference unsupported for expression: " exp
            | NONE => get_error_msg "type inference failed for expression: " exp)
          | _ => get_error_msg "type inference failed, since expression contains binop on constants: " exp)
        | NONE => NONE_msg ("unknown optype: "++optype))
      | NONE_msg op2_msg => NONE_msg op2_msg)
    | NONE_msg op1_msg => NONE_msg op1_msg)
  (* Enumeration type value *)
  (* TODO: Is this the only thing encoded by type_member? *)
  | Array [String "type_member";
           Object [("tags", tags);
                   ("type", type);
                   ("name", name)]] =>
   (case petr4_parse_bare_name type of
    | SOME enum_type_name =>
     (case petr4_parse_name name of
      | SOME enum_field_name =>
       (case ALOOKUP (SND enummap) enum_type_name of
        | SOME enum_type_map =>
         (case ALOOKUP enum_type_map enum_field_name of
          | SOME enum_val =>
           SOME_msg (INL (e_v enum_val))
          | NONE => NONE_msg ("enumeration type map of "++(enum_type_name++(" does not contain the field "++enum_field_name))))
        | NONE => NONE_msg ("enumeration type map does not contain the type "++enum_type_name))
      | NONE => get_error_msg "could not parse field name: " name)
    | NONE => get_error_msg "could not parse type name: " type)
  (* Error *)
  | Array [String "error_member";
           Object [("tags", tags);
                   ("err", name)]] =>
   (case petr4_parse_name name of
    | SOME error_name =>
     (case ALOOKUP (SND enummap) "error" of
      | SOME error_map =>
       (case ALOOKUP error_map error_name of
        | SOME error_val =>
         SOME_msg (INL (e_v error_val))
        | NONE => NONE_msg "")
      | NONE => NONE_msg "enumeration type map does not contain the error type.")
    | NONE => get_error_msg "could not parse name: " name)
  (* Function call *)
  | Array [String "call";
           Object [("tags", tags);
                   ("func", func_name);
                   ("type_args", Array tyargs);
                   ("args", Array args)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap) (func_name, NONE) of
    | SOME_msg (INL res_func_name) =>
     (case exp_to_funn vtymap res_func_name of
      | SOME (SOME res_func_name', NONE) =>
       (case petr4_parse_args (tyenv, enummap, vtymap) (ZIP (args, REPLICATE (LENGTH args) NONE)) of
        | SOME_msg res_args =>
           SOME_msg (INL (e_call res_func_name' res_args))
        | NONE_msg func_name_msg => NONE_msg ("could not parse function call arguments: "++func_name_msg))
      (* isValid is modeled in HOL4P4 as a method call *)
      | SOME (SOME res_isvalid, SOME isvalid_arg) =>
       SOME_msg (INL (e_call res_isvalid [isvalid_arg]))
      | _ => get_error_msg "could not parse called function name: " func_name)
    | _ => get_error_msg "unknown format of called function name: " func_name)
  | _ => get_error_msg "unknown JSON format of expression: " exp) /\
(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
(* TODO: Why should this do any type inference? Can that be restricted to parse_expression_gen? *)
 (petr4_parse_args (tyenv, enummap, vtymap) [] =
  SOME_msg []) /\
 (petr4_parse_args (tyenv, enummap, vtymap) (h::t) =
  case h of
  | (Array [String argtype; Object [("tags", tags); ("value", exp)]], p_tau_opt) =>
   if argtype = "Expression" then
    case petr4_parse_expression_gen (tyenv, enummap, vtymap) (exp, NONE) of
     | SOME_msg (INL exp_res) =>
      (* TODO: Check if p_tau_opt is a parameter, then specialise it in t if that is the case *)
      (case petr4_parse_args (tyenv, enummap, vtymap) t of
       | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
       | NONE_msg exps_msg => NONE_msg exps_msg)
     | SOME_msg (INR c) =>
      (case p_tau_opt of
       | SOME (p_tau_bit n) =>
        (case petr4_parse_args (tyenv, enummap, vtymap) t of
         | SOME_msg exps_res => SOME_msg ((e_v (v_bit (fixwidth n (n2v c), n)))::exps_res)
         | NONE_msg exps_msg => NONE_msg exps_msg)
       | SOME other_tau => get_error_msg "non-bitstring type inference unsupported for exp: " exp
       | NONE => get_error_msg "type inference information missing for function argument: " exp)
     | NONE_msg exp_msg => NONE_msg ("could not parse arguments: "++exp_msg)
   else NONE_msg ("unsupported argument type: "++argtype)
  | _ => get_error_msg "unknown JSON format of argument: " (FST h)) (*/\
(petr4_parse_expressions_gen (tyenv, enummap, vtymap) [] = SOME_msg []) /\
(petr4_parse_expressions_gen (tyenv, enummap, vtymap) ((h1, h2)::t) =
 case petr4_parse_expression_gen (tyenv, enummap, vtymap) (h1, h2) of
  | SOME_msg exp_res =>
   (case petr4_parse_expressions_gen (tyenv, enummap, vtymap) t of
    | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
    | NONE_msg exps_msg => NONE_msg exps_msg)
  | NONE_msg exp_msg => NONE_msg ("could not parse expressions: "++exp_msg)) *)
`
cheat
;

(* TODO: Why does this not use tyenv? Remove tyenv? *)
Definition petr4_parse_expression_def:
 petr4_parse_expression (tyenv, enummap:enummap, vtymap) (exp, tau_opt) =
  case petr4_parse_expression_gen (tyenv, enummap, vtymap) (exp, tau_opt) of
  | SOME_msg (INR n) => get_error_msg "no type inference information provided for integer constant: " exp
  | SOME_msg (INL exp) => SOME_msg exp
  | NONE_msg exp_msg => NONE_msg ("could not parse value: "++exp_msg)
End

Definition petr4_parse_expressions_def:
 (petr4_parse_expressions (tyenv, enummap, vtymap) [] =
  SOME_msg []) /\
 (petr4_parse_expressions (tyenv, enummap, vtymap) ((h1, h2)::t) =
  case petr4_parse_expression (tyenv, enummap, vtymap) (h1, h2) of
   | SOME_msg exp_res =>
    (case petr4_parse_expressions (tyenv, enummap, vtymap) t of
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

(* NOTE: Should vtymap be needed at top level?
 *       Remove tyenv, doesn't seem to be needed? *)
Definition petr4_parse_value_def:
 petr4_parse_value (tyenv, enummap:enummap, vtymap) (exp, tau_opt) =
  case petr4_parse_expression_gen (tyenv, enummap, vtymap) (exp, tau_opt) of
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
(* TODO: Update vtymap here? *)
Definition petr4_constant_to_scopeupdate_def:
 petr4_constant_to_scopeupdate (tyenv, enummap, vtymap) json =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"; "value"] json of
  | SOME [tags; annot; json_type; name; json_value] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau =>
     (case petr4_parse_name name of
      | SOME c_name =>
       (* TODO: No type inference for global constants? *)
       (case petr4_parse_value (tyenv, enummap, vtymap) (json_value, NONE) of
        | SOME_msg value => SOME_msg (varn_name c_name, value)
        | NONE_msg val_msg => NONE_msg val_msg)
      | NONE => get_error_msg "could not parse name: " name)
    | NONE => get_error_msg "could not parse type: " json_type)
  | _ => get_error_msg "unknown JSON format of constant: " json
End

(* This is used to parse global constants *)
Definition petr4_parse_constant_def:
 petr4_parse_constant (tyenv, enummap, vtymap, gscope) constant =
  case petr4_constant_to_scopeupdate (tyenv, enummap, vtymap) constant of
   | SOME_msg (varn, val) =>
    (case val of
     | INL v =>
      (case v_to_tau v of
       | SOME tau =>
        SOME_msg (AUPDATE vtymap (varn, parameterise_tau tau), AUPDATE gscope (varn, val))
       | NONE => get_error_msg "unsupported type of constant: " constant)
     | INR n => SOME_msg (vtymap, AUPDATE gscope (varn, val)))
   | NONE_msg const_msg => NONE_msg ("Could not parse constant: "++const_msg) (* TODO: Print constant name using nested msg *)
End

(*******************)
(* Struct + Header *)

(* TODO: This should work with nested pre-defined header types, but can you write them in-place? *)
Definition petr4_parse_struct_field_def:
 petr4_parse_struct_field tyenv struct_field =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"] struct_field of
  | SOME [tags; annot; json_field_type; name] =>
   (case petr4_parse_ptype F tyenv json_field_type of
    | SOME tau =>
     (case petr4_parse_name name of
      | SOME field_name =>
       SOME_msg (field_name, tau)
      | NONE => get_error_msg "could not parse name: " name)
    | NONE => get_error_msg "could not parse struct field type: " json_field_type)
  | _ => NONE_msg "could not parse struct field"
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
  case json_parse_obj ["tags"; "annotations"; "name"; "fields"] struct of
  | SOME [tags; annot; name; Array struct_fields] =>
   (case petr4_parse_name name of
    | SOME struct_name =>
     (case petr4_parse_struct_fields tyenv struct_fields of
      | SOME_msg struct_name_tau_list => SOME_msg (struct_name, p_tau_xtl struct_ty struct_name_tau_list)
      | NONE_msg msg => NONE_msg msg)
    | NONE => get_error_msg "could not parse name: " name)
  | _ => NONE_msg "could not parse struct JSON object"
End

Definition petr4_parse_struct_def:
 petr4_parse_struct tyenv struct struct_ty =
  case petr4_struct_to_tyenvupdate tyenv struct struct_ty of
   | SOME_msg (struct_name, tau) => SOME_msg (AUPDATE tyenv (struct_name, tau))
   | NONE_msg msg => NONE_msg ("Could not parse struct: "++msg)
End

(**********************)
(* Common: statements *)

(* Like ALOOKUP, but also requires the number of arguments to match
 * Required due to overloaded function names, e.g. extract in packet_in *)
Definition find_fty_match_args_def:
 find_fty_match_args ftymap funn numargs =
  case FIND (\ (funn', (tyargs', tyret')). if funn = funn' then (numargs = LENGTH tyargs') else F) ftymap of
  | SOME fty => SOME (SND fty)
  | NONE => NONE
End

Definition petr4_parse_method_call_def:
 petr4_parse_method_call (tyenv, enummap, vtymap, ftymap, gscope, apply_map) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, func); (* Expression: either a name or a member (in case of extern object's method) *)
     (f2, tyargs); (* TODO: Type arguments. Typically an empty list: currently thrown away *)
     (f3, Array args)] => (* Argument list: typically expressions *)
   if f1 = "func" then
    (if f2 = "type_args" then
     (if f3 = "args" then
      (case petr4_parse_expression (tyenv, enummap, vtymap) (func, NONE) of
       | SOME_msg exp =>
        (case exp_to_funn vtymap exp of
         | SOME (SOME funn, obj_opt) =>
          (case find_fty_match_args ftymap funn (LENGTH args) of
           | SOME (arg_tys, ret_ty) =>
            (case petr4_parse_args (tyenv, enummap, vtymap) (ZIP (args, MAP SOME arg_tys)) of
             | SOME_msg res_args =>
              (case funn of
               (* Extern object method *)
               | (funn_ext ext_name extfun_name) =>
                (case obj_opt of
                 | SOME obj =>
                  SOME_msg (stmt_ass lval_null (e_call funn (obj::res_args)))
                 | NONE => get_error_msg "no object provided for extern object method call: " func)
               (* Method without associated object *)
               (* TODO: This can either be an extern or not... *)
               (* Note special treatment of verify *)
               | (funn_name fun_name) =>
                (if fun_name = "verify" then
                  (* TODO: Make error check for res_args format *)
                  SOME_msg (stmt_verify (EL 0 res_args) (EL 1 res_args))
                 else 
                  SOME_msg (stmt_ass lval_null (e_call funn res_args)))
               | _ => get_error_msg "unknown type of method call: " func)
             | NONE_msg args_msg => NONE_msg ("could not parse method call: "++args_msg))
           | NONE => get_error_msg "type inference information not found for method call: " func)
         (* Apply *)
         | SOME (NONE, SOME app_exp) =>
           (case app_exp of
            | (e_var (varn_name tbl_name)) =>
             (case ALOOKUP apply_map tbl_name of
              | SOME keys =>
               SOME_msg (stmt_app tbl_name keys)
              | NONE => NONE_msg ("could not find entry of table name "++tbl_name++" in apply map"))
            | _ => get_error_msg "could not parse table name: " func)
         | _ => get_error_msg "could not parse into funn: " func)
       | NONE_msg func_msg => NONE_msg ("could not parse method call: "++func_msg))
      else NONE_msg ("unknown JSON object field of method call: "++f3))
     else NONE_msg ("unknown JSON object field of method call: "++f2))
   else NONE_msg ("unknown JSON object field of method call: "++f1)
  | _ => get_error_msg "unknown JSON format of method call: " (Object stmt_details)
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

(* TODO: Expand... *)
Definition infer_rhs_type_def:
 infer_rhs_type vtymap lval =
  case lval of
  | lval_varname varn =>
   ALOOKUP vtymap varn
  | lval_field lval fld =>
   (case infer_rhs_type vtymap lval of
    | SOME (p_tau_xtl struct_ty flds) =>
     ALOOKUP flds fld
    | _ => NONE)
  | _ => NONE
End

Definition petr4_parse_assignment_def:
 petr4_parse_assignment (tyenv, enummap, vtymap, gscope) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, lhs); (* Left-hand side: expression, should be lval *)
     (f2, rhs)] => (* Right-hand side: expression *)
   if f1 = "lhs" then
    (if f2 = "rhs" then
     (case petr4_parse_expression (tyenv, enummap, vtymap) (lhs, NONE) of
      | SOME_msg lhs_res =>
       (case exp_to_lval lhs_res of
        | SOME lval => 
         (case infer_rhs_type vtymap lval of
          | SOME p_tau =>
           (case petr4_parse_expression (tyenv, enummap, vtymap) (rhs, SOME p_tau) of
            | SOME_msg rhs_res => SOME_msg (stmt_ass lval rhs_res)
            | NONE_msg rhs_msg => NONE_msg ("could not parse RHS of assignment: "++rhs_msg))
          | NONE => get_error_msg "no type inference information found for lval: " lhs)
        | NONE => get_error_msg "could not parse into lval: " lhs)
      | NONE_msg lhs_msg => NONE_msg ("could not parse LHS of assignment: "++lhs_msg))
     else NONE_msg ("unknown JSON object field of assignment: "++f2))
   else NONE_msg ("unknown JSON object field of assignment: "++f1)
  | _ => get_error_msg "unknown JSON format of assignment: " (Object stmt_details)
End

Definition petr4_parse_return_def:
 petr4_parse_return (tyenv, enummap, vtymap, gscope) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, exp)] => (* Right-hand side: expression *)
   if f1 = "expr" then
     (case petr4_parse_expression (tyenv, enummap, vtymap) (exp, NONE) of
      | SOME_msg exp_res => SOME_msg (stmt_ret exp_res)
      | NONE_msg exp_msg => NONE_msg ("could not parse return expression: "++exp_msg))
   else NONE_msg ("unknown JSON object field of return: "++f1)
  | _ => get_error_msg "unknown JSON format of return: " (Object stmt_details)
End

Definition petr4_parse_var_def:
 petr4_parse_var (tyenv, enummap, vtymap) var =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"; "init"] var of
  | SOME [tags; annot; json_type; name; opt_init] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau_var =>
(* TODO: Not needed?
     (case petr4_parse_type_name json_type of
      | SOME type_name =>
*)
       (case petr4_parse_name name of
        | SOME var_name =>
         (case opt_init of
          | Null =>
           SOME_msg (varn_name var_name, tau_var, NONE)
          | val_exp =>
           (case petr4_parse_value (tyenv, enummap, vtymap) (val_exp, SOME (parameterise_tau tau_var)) of
            | SOME_msg (INL val) =>
             SOME_msg (varn_name var_name, tau_var, SOME val)
            | SOME_msg (INR n) => get_error_msg "type inference failed for integer constant: " val_exp
            | NONE_msg init_val_msg => NONE_msg ("could not parse initial value: "++init_val_msg)))
        | NONE => get_error_msg "could not parse name: " name)
(*
      | _ => get_error_msg "could not parse type name: " json_type)
*)
    | NONE => get_error_msg "could not parse type: " json_type)
  | _ => get_error_msg "unknown JSON format of variable: " var
End

Definition p4_seq_append_stmt_def:
 p4_seq_append_stmt stmt1 stmt2 =
  case (stmt1, stmt2) of
  | (stmt_empty, stmt_empty) => stmt_empty
  | (stmt_empty, stmt2) => stmt2
  | (stmt1, stmt_empty) => stmt1
  | _ => (stmt_seq stmt1 stmt2)
End

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
val _ = TotalDefn.tDefine "petr4_parse_stmts"
 `(petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) [] = SOME_msg stmt_empty) /\
  (petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) (h::t) =
  case h of
  | Array [String stmt_name; Object stmt_details] =>
   if stmt_name = "method_call" then
    (case petr4_parse_method_call (tyenv, enummap, vtymap, ftymap, gscope, apply_map) stmt_details of
     | SOME_msg call_res =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
       | SOME_msg stmts_res =>
        SOME_msg (p4_seq_append_stmt call_res stmts_res)
       | NONE_msg stmts_msg => NONE_msg stmts_msg)
     | NONE_msg call_msg => NONE_msg call_msg)
   else if stmt_name = "assignment" then
    (case petr4_parse_assignment (tyenv, enummap, vtymap, gscope) stmt_details of
     | SOME_msg ass_res =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
       | SOME_msg stmts_res =>
        SOME_msg (p4_seq_append_stmt ass_res stmts_res)
       | NONE_msg stmts_msg => NONE_msg stmts_msg)
     | NONE_msg ass_msg => NONE_msg ass_msg)
   (* Note: conditional statement is recursive *)
   else if stmt_name = "conditional" then
    case stmt_details of
    | [(f0, tags); (* No check for this, since it's only thrown away *)
       (f1, cond); (* Condition: expression *)
       (f2, true_case); (* True case: statement *)
       (f3, false_case)] => (* False case: statement *)
     if f1 = "cond" then
      (if f2 = "tru" then
       (if f3 = "fls" then
        (case petr4_parse_expression (tyenv, enummap, vtymap) (cond, NONE) of
         | SOME_msg cond_res =>
          (* TODO: Will this work, since the cases are always a singleton list of a block statement? *)
          (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) [true_case] of
           | SOME_msg true_case_res =>
            (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) [false_case] of
             | SOME_msg false_case_res =>
              (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
               | SOME_msg stmts_res =>
                SOME_msg (p4_seq_append_stmt (stmt_cond cond_res true_case_res false_case_res) stmts_res)
               | NONE_msg stmts_msg => NONE_msg stmts_msg)
             | NONE_msg false_case_msg =>
              NONE_msg ("could not parse else-case of conditional statement: "++false_case_msg))
           | NONE_msg true_case_msg => NONE_msg ("could not parse then-case of conditional statement: "++true_case_msg))
         | NONE_msg cond_msg => NONE_msg ("could not parse condition of conditional statement: "++cond_msg))
        else NONE_msg ("unknown JSON object field of conditional: "++f3))
       else NONE_msg ("unknown JSON object field of conditional: "++f2))
     else NONE_msg ("unknown JSON object field of conditional: "++f1)
    | _ => get_error_msg "unknown JSON format of conditional: " (Object stmt_details)
   else if stmt_name = "block" then
    case stmt_details of
    | [("tags", tags); (f1, block)] =>
     if f1 = "block" then
      (case json_parse_obj ["tags"; "annotations"; "statements"] block of
       | SOME [tags; annotations; Array stmts] =>
        (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) stmts of
         | SOME_msg stmts_res => 
          (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
           | SOME_msg t_res =>
            SOME_msg (p4_seq_append_stmt (stmt_block [] stmts_res) t_res)
           | NONE_msg t_msg => NONE_msg t_msg)
         | NONE_msg stmts_msg => NONE_msg ("could not parse block: "++stmts_msg)
        )
       | _ => get_error_msg "unknown JSON format of block: " block
      )
     else NONE_msg ("unknown JSON object field of block: "++f1)
    | _ => get_error_msg "unknown JSON format of block: " (Object stmt_details)
   else if stmt_name = "return" then
    (case petr4_parse_return (tyenv, enummap, vtymap, gscope) stmt_details of
     | SOME_msg ret_res =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
       | SOME_msg stmts_res =>
        SOME_msg (p4_seq_append_stmt ret_res stmts_res)
       | NONE_msg stmts_msg => NONE_msg stmts_msg)
     | NONE_msg ret_msg => NONE_msg ret_msg)
   (* Since declaration must always be at the start of a block, we create a
    * new block after every declaration *)
   else if stmt_name = "declaration" then
    case stmt_details of
    | [("tags", tags);
       ("decl", decl)] =>
     (case json_parse_arr "Variable" SOME decl of
      | SOME decl_obj =>
       (case petr4_parse_var (tyenv, enummap, vtymap) decl_obj of
        | SOME_msg (varn, tau, init_val_opt) => 
         (case petr4_parse_stmts (tyenv, enummap, AUPDATE vtymap (varn, parameterise_tau tau), ftymap, gscope, apply_map) t of
          | SOME_msg stmts_res =>
           (case init_val_opt of
            | SOME init_val =>
             SOME_msg (stmt_block [(varn, tau)] (stmt_seq (stmt_ass (lval_varname varn) (e_v init_val)) stmts_res))
            | NONE => SOME_msg (stmt_block [(varn, tau)] stmts_res))
          | NONE_msg stmts_msg => NONE_msg stmts_msg)
        | NONE_msg varn_tau_msg => NONE_msg ("could not parse declaration: "++varn_tau_msg))
      | _ => get_error_msg "unknown JSON format of declaration: " decl)
    | _ => get_error_msg "unknown JSON format of declaration: " (Object stmt_details)
   else if stmt_name = "empty_statement" then
    case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
    | SOME_msg stmts_res =>
     SOME_msg (p4_seq_append_stmt stmt_empty stmts_res)
    | NONE_msg stmts_msg => NONE_msg stmts_msg
   else NONE_msg ("unknown statement name: "++stmt_name)
  | Null =>
   (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, apply_map) t of
    | SOME_msg stmts_res =>
     SOME_msg (p4_seq_append_stmt stmt_empty stmts_res)
    | NONE_msg stmts_msg => NONE_msg stmts_msg)
  | _ => get_error_msg "unknown JSON format of statement: " h)
(* /\
 (petr4_parse_stmts (tyenv, enummap, vtymap, gscope, apply_map) [] =
  SOME_msg []) /\
 (petr4_parse_stmts (tyenv, enummap, vtymap, gscope, apply_map) (h::t) =
  case petr4_parse_stmts (tyenv, enummap, vtymap, gscope, apply_map) h of
   | SOME_msg stmt_res =>
    (case petr4_parse_stmts (tyenv, enummap, vtymap, gscope, apply_map) t of
     | SOME_msg stmts_res => SOME_msg (stmt_res::stmts_res)
     | NONE_msg stmts_msg => NONE_msg stmts_msg)
   | NONE_msg stmt_msg => NONE_msg ("could not parse stmts: "++stmt_msg))*)`
cheat
;
(*
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
*)


(********************************************************)
(* Functions, actions, extern functions without objects *)

(* Enumeration type for function types *)
Datatype:
 funtype_t =
    funtype_function
  | funtype_action
  | funtype_ext_function
  | funtype_ext_obj_function string
  | funtype_ext_obj_constructor string
End

Definition petr4_parse_dir_def:
 petr4_parse_dir dir =
  case dir of
  | Null => SOME_msg d_none
  | Array [String some_dir; tags_obj] =>
   if some_dir = "In" then SOME_msg d_in
   else if some_dir = "InOut" then SOME_msg d_inout
   else if some_dir = "Out" then SOME_msg d_out
   else NONE_msg ("unknown direction name: "++some_dir)
  | _ => get_error_msg "unknown JSON format of direction: " dir
End

(* TODO: Parse optional default value instead of throwing away *)
(* This yields a p_tau list *)
Definition petr4_parse_p_params_def:
 (petr4_parse_p_params ignore_tyspec tyenv [] = SOME_msg ([], [])) /\
 (petr4_parse_p_params ignore_tyspec tyenv (h::t) =
   case json_parse_obj ["tags"; "annotations"; "direction"; "typ"; "variable"; "opt_value"] h of
   | SOME [tags; annot; dir_opt; type; name; opt_value] =>
    (case petr4_parse_dir dir_opt of
     | SOME_msg p_dir =>
      (case petr4_parse_ptype ignore_tyspec tyenv type of
       | SOME p_type =>
        (case petr4_parse_name name of
         | SOME p_name =>
          (case petr4_parse_p_params ignore_tyspec tyenv t of
           | SOME_msg (res_params, res_vty_updates) =>
            SOME_msg ((p_name, p_dir)::res_params, (varn_name p_name, p_type)::res_vty_updates)
           | NONE_msg err_msg_params => NONE_msg err_msg_params)
         | NONE => get_error_msg "could not parse name: " name)
       | NONE => get_error_msg "could not parse type: " type)
     | NONE_msg err_msg_dir => NONE_msg err_msg_dir)
   | _ => get_error_msg "could not parse parameters: " h)
End

(* TODO: Not needed anymore? *)
Definition update_vtymap_fun_def:
 (update_vtymap_fun vty_updates funtype =
  case funtype of
  | funtype_action => vty_updates
  | funtype_function => vty_updates
  | funtype_ext_function => vty_updates
  | funtype_ext_obj_function obj_name => []
  | funtype_ext_obj_constructor obj_name => [])
End

Definition get_funn_name_def:
 (get_funn_name funtype f_name =
  case funtype of
  | funtype_action => (funn_name f_name)
  | funtype_function => (funn_name f_name)
  | funtype_ext_function => (funn_name f_name)
  | funtype_ext_obj_function obj_name => (funn_ext obj_name f_name)
  | funtype_ext_obj_constructor obj_name => (funn_inst obj_name))
End

(* Parses the shared parts of actions and functions *)
(* TODO: Rename this *)
Definition petr4_parse_fun_body_def:
 petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (body, name, params, funtype) =
  case json_parse_obj ["tags"; "annotations"; "statements"] body of
   | SOME [body_tags; body_annot; Array stmts] =>
    (case petr4_parse_name name of
     | SOME fa_name =>
      (case petr4_parse_p_params F tyenv params of
       | SOME_msg (fa_params, p_vty_updates) =>
        (case petr4_parse_stmts (tyenv, enummap, AUPDATE_LIST vtymap (update_vtymap_fun p_vty_updates funtype), ftymap, gscope, apply_map) stmts of
         | SOME_msg fa_body => SOME_msg ((fa_name, (fa_body, fa_params)),
                                         (get_funn_name funtype fa_name, (MAP SND p_vty_updates, tau_bot)))
         | NONE_msg stmts_msg => NONE_msg stmts_msg)
       | NONE_msg params_msg => NONE_msg params_msg)
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "unknown JSON format of function or action body: " body
End

(* TODO: Add return statements as appropriate *)
(* Used by functions for parsing top-level functions and similar, also used directly
 * for parsing block-local actions and extern object methods *)
Definition petr4_fun_to_fmapupdate_def:
 petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) fun funtype =
  case funtype of
  | funtype_action =>
   (case json_parse_obj ["tags"; "annotations"; "name"; "params"; "body"] fun of
    | SOME [tags; annot; name; Array params; body] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (body, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of action: " fun)
  | funtype_function =>
   (case json_parse_obj ["tags"; "return"; "name"; "type_params"; "params"; "body"] fun of
    | SOME [tags; ret_ty; name; Array typarams; Array params; body] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (body, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of function: " fun)
  | funtype_ext_function =>
   (case json_parse_obj ["tags"; "annotations"; "return"; "name"; "type_params"; "params"] fun of
    | SOME [tags; annot; ret_ty; name; Array typarams; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern function: " fun)
  | funtype_ext_obj_function obj_name =>
   (case json_parse_obj ["tags"; "annotations"; "return"; "name"; "type_params"; "params"] fun of
    | SOME [tags; annot; ret_ty; name; Array typarams; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern function: " fun)
  | funtype_ext_obj_constructor obj_name =>
   (case json_parse_obj ["tags"; "annotations"; "name"; "params"] fun of
    | SOME [tags; annot; name; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern constructor: " fun)
End

(* TODO: Decide whether to put action in global or local function map *)
(* Parses a top-level action (note that this can't see any tables, since those can only be defined in control blocks) *)
Definition petr4_parse_action_def:
 petr4_parse_action (tyenv, enummap, vtymap, ftymap, fmap, gscope) action =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, []) action funtype_action of
   | SOME_msg (fmap_upd, ftymap_upd) =>
    SOME_msg (ftymap_upd::ftymap, AUPDATE fmap fmap_upd)
   | NONE_msg msg => NONE_msg ("Could not parse action: "++msg)
End

(* TODO: Decide whether to put function in global or local function map *)
(* TODO: Set return type properly *)
(* Parses a top-level function *)
Definition petr4_parse_function_def:
 petr4_parse_function (tyenv, enummap, vtymap, ftymap, fmap, gscope) function =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, []) function funtype_function of
   | SOME_msg (fmap_upd, (f_name, (f_argtys, _))) =>
    SOME_msg ((f_name, (f_argtys, tau_bot))::ftymap, AUPDATE fmap fmap_upd)
   | NONE_msg msg => NONE_msg ("Could not parse function: "++msg)
End

(* TODO: Decide whether to put function in global or local function map *)
(* TODO: Set return type properly *)
(* Parses a top-level extern function *)
Definition petr4_parse_extfun_def:
 petr4_parse_extfun (tyenv, enummap, vtymap, ftymap, fmap, gscope) extfun =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, []) extfun funtype_ext_function of
   | SOME_msg ((fa_name, (fa_body, fa_params)), (f_name, (f_argtys, _))) =>
    SOME_msg ((f_name, (f_argtys, tau_bot))::ftymap, AUPDATE fmap (fa_name, (stmt_ext, fa_params)))
   | NONE_msg msg => NONE_msg ("Could not parse extern function: "++msg)
End


(***************)
(* Block types *)

Definition petr4_parse_type_params_def:
 (petr4_parse_type_params [] = SOME_msg []) /\
 (petr4_parse_type_params (h::t) =
   case petr4_parse_name h of
   | SOME typaram =>
    (case petr4_parse_type_params t of
     | SOME_msg res_msg => SOME_msg (typaram::res_msg)
     | NONE_msg err_msg => NONE_msg err_msg)
   | _ => get_error_msg "could not parse block type parameter name: " h)
End

Definition petr4_parametrize_tyenv_def:
 petr4_parametrize_tyenv tyenv l =
  AUPDATE_LIST tyenv (MAP ( \ el. (el, p_tau_par el)) l)
End

(* Note: this uses a local, parametrized tyenv *)
Definition petr4_parse_blocktype_params_def:
 (petr4_parse_blocktype_params ptyenv [] = SOME_msg []) /\
 (petr4_parse_blocktype_params ptyenv (h::t) =
   (* TODO: Parse optional default value instead of throwing away *)
   case json_parse_obj ["tags"; "annotations"; "direction"; "typ"; "variable"; "opt_value"] h of
   | SOME [tags; annot; dir_opt; json_type; name; p_opt_value] =>
    (case petr4_parse_dir dir_opt of
     | SOME_msg p_dir =>
      (case petr4_parse_ptype F ptyenv json_type of
       | SOME p_type =>
        (case petr4_parse_name name of
         | SOME p_name =>
          (case petr4_parse_blocktype_params ptyenv t of
           | SOME_msg res_msg => SOME_msg ((p_name, p_dir, p_type)::res_msg)
           | NONE_msg err_msg_params => NONE_msg err_msg_params)
         | NONE => get_error_msg "could not parse name: " name)
       | NONE => get_error_msg "could not parse type: " json_type)
     | NONE_msg err_msg_dir => NONE_msg ("could not parse direction: "++err_msg_dir))
   | _ => get_error_msg "could not parse block type parameters: " h)
End

(* TODO: Keep parametrized type environment in parsed block type? *)
Definition petr4_blocktype_to_bltymapupdate_def:
 petr4_blocktype_to_bltymapupdate (tyenv, fmap, bltymap, gscope) blocktype =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params"] blocktype of
  | SOME [tags; annot; name; Array typarams; Array blparams] =>
   (case petr4_parse_name name of
    | SOME blty_name =>
     (case petr4_parse_type_params typarams of
      | SOME_msg blty_typarams =>
       (case petr4_parse_blocktype_params (petr4_parametrize_tyenv tyenv blty_typarams) blparams of
        | SOME_msg blty_blparams => SOME_msg (blty_name, (blty_typarams, blty_blparams))
        | NONE_msg blparams_msg => NONE_msg (blparams_msg++" while parsing block type "++blty_name))
      | NONE_msg typarams_msg => NONE_msg (typarams_msg++" while parsing block type "++blty_name))
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown JSON format of block type: " blocktype
End

Definition petr4_parse_block_type_def:
 petr4_parse_block_type (tyenv, fmap, bltymap, gscope) blty blocktype_details =
  case petr4_blocktype_to_bltymapupdate (tyenv, fmap, bltymap, gscope) blocktype_details of
   | SOME_msg (blty_name, (blty_typarams, blty_blparams)) =>
    SOME_msg (AUPDATE bltymap (blty_name, (blty, blty_typarams, blty_blparams)))
   | NONE_msg msg => NONE_msg ("Could not parse block type: "++msg)
End

(*****************)
(* Extern object *)

(* TODO: Use json_parse_arr_list *)
(* Note we don't care about function map updates, only function type map updates, since externs
 * will be handled separately anyway *)
Definition petr4_parse_ext_methods_def:
 (petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap) ext_name [] =
  SOME_msg ftymap) /\
 (petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap) ext_name (h::t) =
  case h of
   | Array [String "Method"; met_obj] =>
    (case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, []:func_map, []:scope, []) met_obj (funtype_ext_obj_function ext_name) of
     | SOME_msg (_, ftymap_upd) =>
      petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap_upd::ftymap) ext_name t
     | NONE_msg m_msg => NONE_msg ("could not parse extern method: "++m_msg))
   | Array [String "Constructor"; con_obj] =>
    (case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, []:func_map, []:scope, []) con_obj (funtype_ext_obj_constructor ext_name) of
     | SOME_msg (_, ftymap_upd) =>
      petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap_upd::ftymap) ext_name t
     | NONE_msg c_msg => NONE_msg ("could not parse extern constructor: "++c_msg))
   | _ => get_error_msg "unknown JSON format of extern method: " h)
End

(* TODO: Add support for type parameters *)
Definition petr4_parse_ext_object_def:
 petr4_parse_ext_object (tyenv, enummap, vtymap, ftymap) ext_obj =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "methods"] ext_obj of
   | SOME [tags; annot; name_obj; Array typarams; Array methods] =>
    (case petr4_parse_name name_obj of
     | SOME ext_name => 
      (case petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap) ext_name methods of
       | SOME_msg ftymap' => 
        SOME_msg (AUPDATE tyenv (ext_name, p_tau_ext ext_name), ftymap')
       | NONE_msg met_msg => NONE_msg ("Could not parse extern methods: "++met_msg))
     | NONE => get_error_msg "Could not parse name: " name_obj)
   | _ => get_error_msg "Could not parse extern object: " ext_obj
End

(**********)
(* Parser *)

(* TODO: Infer types of arguments *)
Definition petr4_parse_inst_def:
 petr4_parse_inst (tyenv, enummap, vtymap, decl_list, inits) inst =
  (* TODO: Use args as needed in constructor *)
  (* TODO: Use init field *)
  case json_parse_obj ["tags"; "annotations"; "type"; "args"; "name"; "init"] inst of
  | SOME [tags; annot; json_type; Array args; name; init] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau_ext =>
     (case petr4_parse_args (tyenv, enummap, vtymap) (ZIP (args, REPLICATE (LENGTH args) NONE)) of
      | SOME_msg res_args => 
       (case petr4_parse_type_name json_type of
        | SOME type_name =>
         (case petr4_parse_name name of
          | SOME inst_name =>
           SOME_msg (decl_list++[(varn_name inst_name, tau_ext)],
                     p4_seq_append_stmt inits (stmt_ass lval_null (e_call (funn_inst type_name) ([e_var (varn_name inst_name)]++res_args))),
                     (varn_name inst_name, p_tau_ext type_name))
          | NONE => get_error_msg "could not parse name: " name)
        | _ => get_error_msg "could not parse type name: " json_type)
      | NONE_msg args_msg => NONE_msg ("could not parse instantiation arguments: "++args_msg))
    | SOME _ => get_error_msg "type of instantiation is not extern: " inst
    | NONE => get_error_msg "could not parse type: " json_type
   )
  | _ => get_error_msg "unknown JSON format of instantiation: " inst
End

(* TODO: This should use enummap... *)
Definition petr4_parse_match_kind_def:
 petr4_parse_match_kind match_kind =
  case petr4_parse_name match_kind of
  | SOME mk_str =>
   if mk_str = "exact"
   then SOME_msg mk_exact
   else if mk_str = "ternary"
   then SOME_msg mk_ternary
   else if mk_str = "lpm"
   then SOME_msg mk_lpm
   else NONE_msg ("unknown match kind: "++mk_str)
  | _ => get_error_msg "unknown JSON format of match kind: " match_kind
End

Definition petr4_parse_keys_def:
 (petr4_parse_keys (tyenv, enummap, vtymap) [] = SOME_msg []) /\
 (petr4_parse_keys (tyenv, enummap, vtymap) (h::t) =
   case json_parse_obj ["tags"; "annotations"; "key"; "match_kind"] h of
   | SOME [tags; annot; key; match_kind] =>
    (case petr4_parse_match_kind match_kind of
     | SOME_msg res_mk =>
      (case petr4_parse_expression (tyenv, enummap, vtymap) (key, NONE) of
       | SOME_msg res_key =>
        (case petr4_parse_keys (tyenv, enummap, vtymap) t of
         | SOME_msg res_msg => SOME_msg ((res_key, res_mk)::res_msg)
         | NONE_msg err_msg => NONE_msg err_msg)
       | NONE_msg key_msg => NONE_msg ("could not parse key: "++key_msg))
     | NONE_msg mk_msg => NONE_msg ("could not parse match kind: "++mk_msg))
   | _ => get_error_msg "unknown JSON format of key: " h)
End

(* TODO: Action argument seems to not be exported by petr4 *)
Definition petr4_parse_default_action_def:
 petr4_parse_default_action (tyenv, enummap, vtymap) default_action =
  (* TODO: Don't throw const away *)
  case json_parse_obj ["tags"; "annotations"; "const"; "name"; "value"] default_action of
  | SOME [tags; annot; const; name; action] =>
   (case petr4_parse_name name of
    | SOME custom_name =>
     if custom_name = "default_action" then
     (case petr4_parse_expression (tyenv, enummap, vtymap) (action, NONE) of
      | SOME_msg (e_call (funn_name action_name) args) =>
       SOME_msg (action_name, args)
      | SOME_msg (e_var (varn_name action_name)) =>
       SOME_msg (action_name, [])
      | _ => get_error_msg "unknown format of default action name: " action)
     else get_error_msg ("unknown table property field ("++(custom_name++"): ")) default_action
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown format of table property field: " default_action
End

(* TODO: Note that this presupposes a default_action field is present if any optional field is *)
(* TODO: Fix this mess... *)
Definition petr4_build_table_def:
 petr4_build_table (tyenv, enummap, vtymap) keys_obj custom_obj_opt custom_obj_opt2 =
  case petr4_parse_keys (tyenv, enummap, vtymap) keys_obj of
  | SOME_msg keys_res =>
   (case custom_obj_opt of
    | SOME custom_obj =>
     (case custom_obj_opt2 of
      | SOME custom_obj2 =>
       (* See if first custom object is an action *)
       (case petr4_parse_default_action (tyenv, enummap, vtymap) custom_obj of
        | SOME_msg default_action =>
         SOME_msg (keys_res, default_action)
       (* If not, second may be an action *)
        | NONE_msg def_act_msg =>
         (case petr4_parse_default_action (tyenv, enummap, vtymap) custom_obj2 of
          | SOME_msg default_action2 =>
           SOME_msg (keys_res, default_action2)
          | NONE_msg def_act_msg2 => NONE_msg ("either "++(def_act_msg++(" or "++def_act_msg2)))))
      | NONE =>
       (case petr4_parse_default_action (tyenv, enummap, vtymap) custom_obj of
        | SOME_msg default_action =>
         SOME_msg (keys_res, default_action)
        | NONE_msg def_act_msg => NONE_msg def_act_msg))
    | NONE =>
     SOME_msg (keys_res, ("NoAction", [])))
  | NONE_msg keys_msg => NONE_msg keys_msg
End

Definition petr4_property_is_key_def:
 petr4_property_is_key prop = 
  case prop of
  | (Array [String "Key"; obj]) => T
  | _ => F
End

Definition petr4_property_is_actions_def:
 petr4_property_is_actions prop = 
  case prop of
  | (Array [String "Actions"; obj]) => T
  | _ => F
End

(* It's a bit inefficient to re-compute this, but it gives a unified solution overall *)
Definition petr4_property_is_default_action_def:
 petr4_property_is_default_action prop = 
  case prop of
  | (Array [String "Custom"; obj]) =>
   (case json_parse_obj ["tags"; "annotations"; "const"; "name"; "value"] obj of
    | SOME [tags; annot; const; name; value] =>
     (case petr4_parse_name name of
      | SOME custom_name =>
       if custom_name = "default_action" then T else F
      | NONE => F)
    | _ => F)
  | _ => F
End

Definition petr4_property_is_size_def:
 petr4_property_is_size prop = 
  case prop of
  | (Array [String "Custom"; obj]) =>
   (case json_parse_obj ["tags"; "annotations"; "const"; "name"; "value"] obj of
    | SOME [tags; annot; const; name; value] =>
     (case petr4_parse_name name of
      | SOME custom_name =>
       if custom_name = "size" then T else F
      | NONE => F)
    | _ => F)
  | _ => F
End

Definition petr4_property_is_entries_def:
 petr4_property_is_entries prop = 
  case prop of
  | (Array [String "Custom"; obj]) =>
   (case json_parse_obj ["tags"; "annotations"; "const"; "name"; "value"] obj of
    | SOME [tags; annot; const; name; value] =>
     (case petr4_parse_name name of
      | SOME custom_name =>
       if custom_name = "entries" then T else F
      | NONE => F)
    | _ => F)
  | _ => F
End

(*
Definition petr4_process_prop_def:
 petr4_process_prop recogniser parser props =
  case FIND_EXTRACT_ONE recogniser props of
  | SOME (e, l') =>
   (case parser e of
    | SOME res => SOME (res, l')
    | NONE => NONE)
  | NONE => NONE
End
*)

Definition petr4_process_key_def:
 petr4_process_key (tyenv, enummap, vtymap) props =
  case FIND_EXTRACT_ONE petr4_property_is_key props of
  | SOME (keys, props') =>
   (case keys of
    | Array [String "Key"; Object [("tags", tags); ("keys", Array keys_obj)]] =>
     (case petr4_parse_keys (tyenv, enummap, vtymap) keys_obj of
      | SOME_msg key_mk_list => SOME_msg (key_mk_list, props')
      | NONE_msg msg => NONE_msg msg)
    | _ => get_error_msg "unknown key property format: " keys)
  | NONE => get_error_msg "zero or duplicate key property fields in table: " (Array props)
End

(* TODO: Add more here later when needed *)
Definition petr4_process_actions_def:
 petr4_process_actions props =
  case FIND_EXTRACT_ONE petr4_property_is_actions props of
  | SOME (actions, props') =>
   SOME_msg props'
  | NONE => get_error_msg "zero or duplicate actions property fields in table: " (Array props)
End

Definition petr4_process_default_action_def:
 petr4_process_default_action (tyenv, enummap, vtymap) props =
  case FIND_EXTRACT_ONE petr4_property_is_default_action props of
  | SOME (default_action, props') =>
   (case default_action of
    | Array [String "Custom"; custom_obj] =>
     (case petr4_parse_default_action (tyenv, enummap, vtymap) custom_obj of
      | SOME_msg (action_name, args) => SOME_msg (SOME (action_name, args), props')
      | NONE_msg msg => NONE_msg msg)
    | _ => get_error_msg "unknown default action property format: " default_action)
  | NONE => SOME_msg (NONE, props)
End

(* TODO: Add stuff here as needed *)
Definition petr4_process_size_def:
 petr4_process_size props = SOME_msg props
End

(* TODO: Add stuff here ASAP to initialise ctrl *)
Definition petr4_process_entries_def:
 petr4_process_entries (tyenv, enummap, vtymap) props = SOME_msg props
(*
  case FIND_EXTRACT_ONE petr4_property_is_entries props of
  | SOME (entries, props') =>
   (case entries of
    | Array [String "Custom"; custom_obj] =>
     (case petr4_parse_entries (tyenv, enummap, vtymap) custom_obj of
      | SOME_msg entries_parsed => SOME_msg (SOME entries_parsed, props')
      | NONE_msg msg => NONE_msg msg)
    | _ => get_error_msg "unknown entries property format: " entries)
  | NONE => SOME_msg (NONE, props)
*)
End

(* TODO: Don't throw away the "actions" field? *)
(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
(* Note: P4 spec says tables don't have to have key fields - then the default action will
 * always be the result of matching *)
Definition petr4_parse_properties_def:
 petr4_parse_properties (tyenv, enummap, vtymap) props =
  let
   (keys_obj', props') = (case props of
    | ((Array [String "Key"; Object [("tags", tags); ("keys", Array keys_obj)]])::t) =>
     (keys_obj, t)
    | _ => ([], props))
  in
   (case props' of
    | ((Array [String "Actions"; actions_obj])::t') =>
     (case t' of
      | ((Array [String "Custom"; custom_obj])::t'') =>
       (case t'' of
        | [Array [String "Custom"; custom_obj2]] =>
         petr4_build_table (tyenv, enummap, vtymap) keys_obj' (SOME custom_obj) (SOME custom_obj2)
        | [] => petr4_build_table (tyenv, enummap, vtymap) keys_obj' (SOME custom_obj) NONE
        | _ => get_error_msg "unknown JSON format of table properties: " (Array props))
      | [] => petr4_build_table (tyenv, enummap, vtymap) keys_obj' NONE NONE
      | _ => get_error_msg "unknown JSON format of table properties: " (Array props))
    | _ => get_error_msg "unknown JSON format of table properties: " (Array props))
End

Definition petr4_parse_table_def:
 petr4_parse_table (tyenv, vtymap) table =
  case json_parse_obj ["tags"; "annotations"; "name"; "properties"] table of
  | SOME [tags; annot; name; Array props] =>
   (* Properties are: Key, Actions, Custom-"size" (optional), Custom-"default_action" (optional?) *)
   (case petr4_parse_name name of
    | SOME tbl_name =>
     (case petr4_parse_properties (tyenv, vtymap) props of
      | SOME_msg (keys, default_action) => SOME_msg ((tbl_name, (SND $ UNZIP keys, default_action)), (tbl_name, FST $ UNZIP keys))
      | NONE_msg prop_msg => NONE_msg ("could not parse properties: "++prop_msg))
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown JSON format of table: " table
End

(* TODO: Use json_parse_arr_list *)
Definition petr4_parse_locals_def:
 (petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope) (b_func_map:b_func_map, tbl_map:tbl_map, decl_list, inits, apply_map) [] =
  SOME_msg (vtymap, ftymap, b_func_map, tbl_map, decl_list, inits, apply_map)) /\
 (petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope) (b_func_map, tbl_map, decl_list, inits, apply_map) (h::t) =
  case h of
   | Array [String "Instantiation"; inst_obj] =>
    (case petr4_parse_inst (tyenv, enummap, vtymap, decl_list, inits) inst_obj of
     | SOME_msg (decl_list', inits', vty_upd) =>
      petr4_parse_locals (tyenv, enummap, AUPDATE vtymap vty_upd, ftymap, fmap, gscope) (b_func_map, tbl_map, decl_list', inits', apply_map) t
     | NONE_msg inst_msg => NONE_msg ("could not parse instantiation: "++inst_msg))
   | Array [String "Action"; act_obj] =>
    (case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map) act_obj funtype_action of
     | SOME_msg (b_func_map_upd, ftymap_upd) =>
      petr4_parse_locals (tyenv, enummap, vtymap, ftymap_upd::ftymap, fmap, gscope) (AUPDATE b_func_map b_func_map_upd, tbl_map, decl_list, inits, apply_map) t
     | NONE_msg f_msg => NONE_msg ("could not parse block-local action: "++f_msg))
   | Array [String "Variable"; var_obj] =>
    (case petr4_parse_var (tyenv, enummap, vtymap) var_obj of
     | SOME_msg (varn, tau, init_opt) =>
      (case init_opt of
       | SOME init_val =>
        petr4_parse_locals (tyenv, enummap, AUPDATE vtymap (varn, parameterise_tau tau), ftymap, fmap, gscope) (b_func_map, tbl_map, decl_list++[(varn, tau)], stmt_seq inits (stmt_ass (lval_varname varn) (e_v init_val)), apply_map) t
       | NONE =>
        petr4_parse_locals (tyenv, enummap, AUPDATE vtymap (varn, parameterise_tau tau), ftymap, fmap, gscope) (b_func_map, tbl_map, decl_list++[(varn, tau)], inits, apply_map) t)
     | NONE_msg var_msg => NONE_msg ("could not parse block-local variable: "++var_msg))
   | Array [String "Table"; tab_obj] =>
    (case petr4_parse_table (tyenv, enummap, vtymap) tab_obj of
     | SOME_msg (tbl_map_entry, apply_map_entry) =>
      petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope) (b_func_map, AUPDATE tbl_map tbl_map_entry, decl_list, inits, AUPDATE apply_map apply_map_entry) t
     | NONE_msg tbl_msg => NONE_msg ("could not parse table: "++tbl_msg))
   | _ => get_error_msg "unknown JSON format of local: " h)
End

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
Definition petr4_parse_matches_def:
 (petr4_parse_matches (tyenv, enummap, vtymap, g_scope) expected_tau [] = SOME_msg []) /\
 (petr4_parse_matches (tyenv, enummap, vtymap, g_scope) expected_tau (h::t) =
  case h of
  | Array [String "Expression";
           Object [("tags", tags); ("expr", exp)]] =>
   (case petr4_parse_expression (tyenv, enummap, vtymap) (exp, SOME expected_tau) of
     | SOME_msg exp_res =>
      (case petr4_parse_matches (tyenv, enummap, vtymap, g_scope) expected_tau t of
       | SOME_msg matches_res => SOME_msg (exp_res::matches_res)
       | NONE_msg matches_msg => NONE_msg matches_msg)
     | NONE_msg exp_msg => NONE_msg ("could not parse select match case: "++exp_msg)
   )
  | _ => get_error_msg "unknown JSON format of select case match: " h)
End

Definition petr4_parse_case_def:
 petr4_parse_case (tyenv, vtymap, g_scope) expected_tau select_case =
  case json_parse_obj ["tags"; "matches"; "next"] select_case of
   | SOME [tags; Array match_exps; name] =>
    (case petr4_parse_matches (tyenv, vtymap, g_scope) expected_tau match_exps of
     | SOME_msg [exp_res] =>
      (case v_of_e exp_res of
       | SOME v =>
        (case petr4_parse_name name of
         | SOME state_name =>       
          SOME_msg (v, state_name)
         | NONE => get_error_msg "could not parse name: " name)
       | NONE => get_error_msg "non-value expressions as select match cases not yet supported: " (Array match_exps))
     | SOME_msg _ => get_error_msg "lists of case matches not yet supported" (Array match_exps)
     | NONE_msg exp_msg => NONE_msg ("could not parse expression: "++exp_msg))
   | _ => get_error_msg "unknown JSON format of case: " select_case
End

Definition petr4_parse_cases_def:
 (petr4_parse_cases (tyenv, vtymap, g_scope) expected_tau [] =
  SOME_msg []) /\
 (petr4_parse_cases (tyenv, vtymap, g_scope) expected_tau (h::t) =
  case petr4_parse_case (tyenv, vtymap, g_scope) expected_tau h of
   | SOME_msg case_res =>
    (case petr4_parse_cases (tyenv, vtymap, g_scope) expected_tau t of
     | SOME_msg cases_res => SOME_msg (case_res::cases_res)
     | NONE_msg cases_msg => NONE_msg cases_msg)
   | NONE_msg case_msg => NONE_msg ("could not parse cases: "++case_msg))
End

(* TODO: Use json_parse_arr_list *)
Definition petr4_parse_trans_def:
 petr4_parse_trans (tyenv, enummap, vtymap, gscope) trans =
  case trans of
  | [String "Direct";
     Object [("tags", tags);
             ("next", next)]] =>
   (case petr4_parse_name next of
    | SOME next_state =>
     SOME_msg (stmt_trans (e_v (v_str next_state)))
    | NONE => get_error_msg "could not parse name: " next)
  | [String "Select";
     Object [("tags", tags);
             ("exprs", Array exps);
             ("cases", Array cases)]] =>
    (case petr4_parse_expressions (tyenv, enummap, vtymap) (ZIP(exps, REPLICATE (LENGTH exps) NONE)) of
     (* TODO: Support multiple expressions *)
     | SOME_msg [exp_res] =>
      (* TODO: Fix this *)
      (case exp_to_p_tau vtymap exp_res of
       | SOME p_tau =>
        (case petr4_parse_cases (tyenv, enummap, vtymap, gscope) p_tau cases of
         | SOME_msg cases_res =>
          (* TODO: Note that reject is always default next state unless otherwise specified...
           * Hard-coded in petr4 semantics or in spec? *)
          SOME_msg (stmt_trans (e_select exp_res cases_res "reject"))
         | NONE_msg cases_msg => get_error_msg (cases_msg++" while parsing transition: ") (Array trans))
       | NONE => get_error_msg "could not parse type of " (Array exps))
     | NONE_msg exps_msg => get_error_msg (exps_msg++" while parsing transition: ") (Array trans)
     | _ => get_error_msg ("lists of expressions in select statements not supported, encountered while parsing transition: ") (Array trans))
  | _ => get_error_msg "unknown JSON format of transition: " (Array trans)
End

Definition petr4_parse_states_def:
 (petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope) (pars_map:pars_map) [] =
  SOME_msg pars_map) /\
 (petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope) pars_map (h::t) =
  case json_parse_obj ["tags"; "annotations"; "name"; "statements"; "transition"] h of
   | SOME [tags; annot; name; Array stmts; Array trans] =>
    (case petr4_parse_name name of
     | SOME state_name =>
      (case petr4_parse_stmts (tyenv,enummap,vtymap,ftymap,gscope,[]) stmts of
       | SOME_msg stmts_res =>
        (case petr4_parse_trans (tyenv,enummap,vtymap,gscope) trans of
         | SOME_msg trans_res =>
          petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope) (AUPDATE pars_map (state_name, stmt_seq stmts_res trans_res)) t
         | NONE_msg trans_msg => NONE_msg ("could not parse parser state: "++trans_msg))
       | NONE_msg stmts_msg => NONE_msg ("could not parse parser state body: "++stmts_msg))
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "unknown JSON format of parser state: " h)
End

Definition petr4_parse_parser_def:
 petr4_parse_parser (tyenv, enummap, vtymap, ftymap, fmap:func_map, bltymap, gscope, pblock_map:pblock_map) parser =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params";
                       "constructor_params"; "locals"; "states"] parser of
   | SOME [tags; annot; name; Array typarams; Array params; Array constructor_params; Array locals; Array states] =>
    (case petr4_parse_name name of
     | SOME parser_name =>
      (* TODO: Modify vtymap directly here instead? *)
      (case petr4_parse_p_params F tyenv params of
       | SOME_msg (pars_params, vty_updates) =>
        (case petr4_parse_locals (tyenv, enummap, AUPDATE_LIST vtymap vty_updates, ftymap, fmap, gscope) ([], [], [], stmt_empty, []) locals of
         | SOME_msg (vtymap', ftymap', b_func_map, tbl_map, decl_list, inits, apply_map) =>
          (case petr4_parse_states (tyenv, enummap, AUPDATE_LIST vtymap' vty_updates, ftymap', gscope) [] states of
           | SOME_msg pars_map =>
            SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, AUPDATE pblock_map (parser_name, (pblock_regular pbl_type_parser pars_params b_func_map decl_list inits pars_map tbl_map)))
           | NONE_msg states_msg => NONE_msg ("Could not parse states: "++states_msg++" while parsing parser "++parser_name))
         | NONE_msg locals_msg => NONE_msg ("Could not parse locals: "++locals_msg++" while parsing parser "++parser_name))
       | NONE_msg blparams_msg => NONE_msg ("Could not parse block parameters: "++blparams_msg++" while parsing parser "++parser_name))
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "Unknown JSON format of parser: " parser
End


(***********)
(* Control *)

Definition petr4_parse_control_def:
 petr4_parse_control (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, pblock_map:pblock_map) control =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params";
                       "constructor_params"; "locals"; "apply"] control of
   | SOME [tags; annot; name; Array typarams; Array params; Array constructor_params; Array locals; apply] =>
    (case json_parse_obj ["tags"; "annotations"; "statements"] apply of 
     | SOME [app_tags; app_annot; Array stmts] =>
      (case petr4_parse_name name of
       | SOME control_name =>
        (* TODO: Check that the parameters are a proper instantiation of the type-parametrized
         * block type parameters? *)
        (* TODO: Modify vtymap directly here instead? *)
        (case petr4_parse_p_params F tyenv params of
         | SOME_msg (ctrl_params, vty_updates) =>
          (case petr4_parse_locals (tyenv, enummap, AUPDATE_LIST vtymap vty_updates, ftymap, fmap, gscope) ([], [], [], stmt_empty, []) locals of
           | SOME_msg (vtymap', ftymap', b_func_map, tbl_map, decl_list, inits, apply_map) =>
            (case petr4_parse_stmts (tyenv, enummap, AUPDATE_LIST vtymap' vty_updates, ftymap', gscope, apply_map) stmts of
             | SOME_msg res_apply =>
              SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, AUPDATE pblock_map (control_name, (pblock_regular pbl_type_control ctrl_params b_func_map decl_list (stmt_seq inits res_apply) ([]:pars_map) tbl_map)))
             | NONE_msg apply_msg => NONE_msg ("Could not parse apply: "++apply_msg++" while parsing control "++control_name))
           | NONE_msg locals_msg => NONE_msg ("Could not parse locals: "++locals_msg++" while parsing control "++control_name))
         | NONE_msg blparams_msg => NONE_msg ("Could not parse block parameters: "++blparams_msg++" while parsing control "++control_name))
       | NONE => get_error_msg "could not parse name: " name)
     | _ => get_error_msg "Unknown JSON format of apply block: " apply)
   | _ => get_error_msg "Unknown JSON format of control: " control
End

(****************)
(* Package type *)

Definition petr4_p_tau_par_to_string_def:
 petr4_p_tau_par_to_string p_tau =
  case p_tau of
  | p_tau_par str => SOME str
  | _ => NONE
End

(* TODO: Write abstraction for "FOLDL with option type" instead *)
Definition petr4_parse_pblock_insts_def:
 (petr4_p_tau_pars_to_string [] = SOME []) /\
 (petr4_p_tau_pars_to_string (h::t) =
   case petr4_p_tau_par_to_string h of
   | SOME res =>
    (case petr4_p_tau_pars_to_string t of
     | SOME res_tl => SOME (res::res_tl)
     | NONE => NONE)
   | NONE => NONE)
End

(* TODO: Create a ptymap, also store parameters for type inference there? *)
Definition petr4_parse_package_type_def:
 petr4_parse_package_type (tyenv, ptymap) package_type =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params"] package_type of
  | SOME [tags; annot; name; type_params; Array params] =>
   (case petr4_parse_p_params T tyenv params of
    | SOME_msg (res_dirs, e_params) =>
     (case petr4_p_tau_pars_to_string (MAP SND e_params) of
      | SOME str_tys =>
       (case petr4_parse_name name of
        | SOME pkg_name =>
         SOME_msg (AUPDATE tyenv (pkg_name, p_tau_pkg pkg_name), AUPDATE ptymap (pkg_name, str_tys))
        | NONE => get_error_msg "Could not parse name: " name)
      | NONE => get_error_msg "Could not parse package type parameters: " (Array params))
    | NONE_msg msg => NONE_msg msg)
  | _ => get_error_msg "Unknown JSON format of package type: " package_type
End

(***************************************)
(* Package/Extern object instantiation *)

(* This parses an expression that can only be an argumentless instantiation into the
 * name of the object being instantiated *)
Definition petr4_parse_pblock_inst_def:
 petr4_parse_pblock_inst pblock_inst =
  case json_parse_arr "Expression" SOME pblock_inst of
  | SOME exp_obj =>
   (case json_parse_obj ["tags"; "value"] exp_obj of
    | SOME [tags; exp] =>
     (case json_parse_arr "instantiation" SOME exp of
      | SOME instantiation_obj =>
       (case json_parse_obj ["tags"; "type"; "args"] instantiation_obj of
        | SOME [tags'; type; args] => petr4_parse_type_name type
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
End

(* TODO: Write abstraction for "FOLDL with option type" instead *)
Definition petr4_parse_pblock_insts_def:
 (petr4_parse_pblock_insts [] = SOME []) /\
 (petr4_parse_pblock_insts (h::t) =
   case petr4_parse_pblock_inst h of
   | SOME res =>
    (case petr4_parse_pblock_insts t of
     | SOME res_tl => SOME (res::res_tl)
     | NONE => NONE)
   | NONE => NONE)
End

Definition petr4_get_arch_block_pbl_def:
 petr4_get_arch_block_pbl bltymap (pbl_name, pbl_type) =
  case ALOOKUP bltymap pbl_type of
   | SOME (type, typarams, params) =>
    SOME (arch_block_pbl pbl_name (MAP (\ (a, b, c). (e_var $ varn_name a)) params))
   | NONE => NONE
End

Definition petr4_get_arch_block_pbls_def:
 (petr4_get_arch_block_pbls _ [] = SOME []) /\
 (petr4_get_arch_block_pbls bltymap ((h1,h2)::t) =
   case petr4_get_arch_block_pbl bltymap (h1,h2) of
   | SOME res =>
    (case petr4_get_arch_block_pbls bltymap t of
     | SOME res_tl => SOME (res::res_tl)
     | NONE => NONE)
   | NONE => NONE)
End

Definition petr4_parse_top_level_inst_def:
 petr4_parse_top_level_inst (tyenv, bltymap, ptymap) inst =
  case json_parse_obj ["tags"; "annotations"; "type"; "args"; "name"; "init"] inst of
  | SOME [tags; annot; type; Array args; name; init] =>
   (case petr4_parse_type_name type of
    | SOME inst_type_name =>
     (case ALOOKUP ptymap inst_type_name of
      | SOME pkg_param_tys =>
       (* Check type of inst in tyenv (extern object or package) *)
       (case ALOOKUP tyenv inst_type_name of
        | SOME (p_tau_pkg pkg_name) =>
         (case petr4_parse_pblock_insts args of
          | SOME args_res =>
           (case petr4_get_arch_block_pbls bltymap (ZIP (args_res, pkg_param_tys)) of
            | SOME ab_pbls => SOME_msg (ab_pbls, pkg_name)
            | NONE => get_error_msg "Could not parse programmable block instantiations: " (Array args))
          | NONE => get_error_msg "Could not parse top-level instantiation arguments: " (Array args))
        | SOME (p_tau_ext ext_name) =>
         (get_error_msg "Top-level extern instantiations currently unsupported by HOL4P4: " inst)
        | _ => get_error_msg "Unknown type of top-level instantiation: " inst)
      | NONE => get_error_msg "Unknown package type: " type)
    | NONE => get_error_msg "Could not parse name: " name)
  | _ => get_error_msg "Unknown JSON format of instantiation: " inst
End


(**********************)
(* Petr4 JSON element *)
(**********************)

(* TODO: Move? *)
Definition vss_add_ff_blocks_def:
 vss_add_ff_blocks [parser; pipe; deparser] =
  [arch_block_inp;
   parser;
   arch_block_ffbl "parser_runtime";
   pipe;
   arch_block_ffbl "pre_deparser";
   deparser;
   arch_block_out]
End

(* TODO: Make wrapper function for errors, so error messages can include the local variable context *)
Definition petr4_parse_element_def:
 petr4_parse_element (tyenv, enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map:pblock_map, arch_pkg_opt, ab_list) json =
  case json of
  | Array [String elem_name; obj] =>
   if elem_name = "Error" then
    (case petr4_parse_error enummap obj of
     | SOME_msg enummap' =>
      SOME_msg (tyenv, enummap', vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "MatchKind" then
    (case petr4_parse_match_kind_typedef enummap obj of
     | SOME_msg enummap' =>
      SOME_msg (tyenv, enummap', vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Enum" then
    (case petr4_parse_enum enummap obj of
     | SOME_msg enummap' =>
      SOME_msg (tyenv, enummap', vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   (* WIP: Extern object types added to the type environment, since parameters to blocks
    * can be of extern type. *)
   else if elem_name = "ExternObject" then
    (case petr4_parse_ext_object (tyenv, enummap, vtymap, ftymap) obj of
     | SOME_msg (tyenv', ftymap') =>
      SOME_msg (tyenv', enummap, vtymap, ftymap', fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "ExternFunction" then
    (case petr4_parse_extfun (tyenv, enummap, vtymap, ftymap, fmap, gscope) obj of
     | SOME_msg (ftymap', fmap') =>
      SOME_msg (tyenv, enummap, vtymap, ftymap', fmap', bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Action" then
    (case petr4_parse_action (tyenv, enummap, vtymap, ftymap, fmap, gscope) obj of
     | SOME_msg (ftymap', fmap') =>
      SOME_msg (tyenv, enummap, vtymap, ftymap', fmap', bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Function" then
    (case petr4_parse_function (tyenv, enummap, vtymap, ftymap, fmap, gscope) obj of
     | SOME_msg (ftymap', fmap') =>
      SOME_msg (tyenv, enummap, vtymap, ftymap', fmap', bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "TypeDef" then
    (case petr4_parse_typedef tyenv obj of
     | SOME_msg tyenv' =>
      SOME_msg (tyenv', enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   (* TODO: Constants are added to the global scope, also vtymap if not arbitrary-length constant... *)
   else if elem_name = "Constant" then
    (case petr4_parse_constant (tyenv, enummap, vtymap, gscope) obj of
     | SOME_msg (vtymap', gscope') =>
      SOME_msg (tyenv, enummap, vtymap', ftymap, fmap, bltymap, ptymap, gscope', pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Struct" then
    (case petr4_parse_struct tyenv obj struct_ty_struct of
     | SOME_msg tyenv' =>
      SOME_msg (tyenv', enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Header" then
    (case petr4_parse_struct tyenv obj struct_ty_header of
     | SOME_msg tyenv' =>
      SOME_msg (tyenv', enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   (* TODO: Fix default parameter values *)
   else if elem_name = "ParserType" then
    (case petr4_parse_block_type (tyenv, fmap, bltymap, gscope) pbl_type_parser obj of
     | SOME_msg bltymap' =>
      SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap', ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   (* TODO: Fix default parameter values *)
   else if elem_name = "ControlType" then
    (case petr4_parse_block_type (tyenv, fmap, bltymap, gscope) pbl_type_control obj of
     | SOME_msg bltymap' =>
      SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap', ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Parser" then
    (case petr4_parse_parser (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, pblock_map) obj of
     | SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, pblock_map) =>
      SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "control" then
    (case petr4_parse_control (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, pblock_map) obj of
     | SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, gscope, pblock_map) =>
      SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "PackageType" then
    (case petr4_parse_package_type (tyenv, ptymap) obj of
     | SOME_msg (tyenv', ptymap') =>
      SOME_msg (tyenv', enummap, vtymap, ftymap, fmap, bltymap, ptymap', gscope, pblock_map, arch_pkg_opt, ab_list)
     | NONE_msg msg => NONE_msg msg)
   else if elem_name = "Instantiation" then
    (case petr4_parse_top_level_inst (tyenv, bltymap, ptymap) obj of
     | SOME_msg (ab_list', pkg_name) =>
      (case arch_pkg_opt of
       (* VSS: Only one top-level package exists *)
       | SOME (arch_vss (NONE)) =>
        SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, SOME (arch_vss (SOME vss_pkg_VSS)), vss_add_ff_blocks ab_list')
       | SOME (arch_vss _) =>
        NONE_msg ("Duplicate top-level package instantiations")
       (* eBPF: Only one top-level package exists *)
       | SOME (arch_ebpf (NONE)) =>
        SOME_msg (tyenv, enummap, vtymap, ftymap, fmap, bltymap, ptymap, gscope, pblock_map, SOME (arch_ebpf (SOME ebpf_pkg_ebpfFilter)), ab_list')
       | SOME (arch_ebpf _) =>
        NONE_msg ("Duplicate top-level package instantiations")
       | _ => NONE_msg ("Unexpected top-level package instantiation"))
     | NONE_msg msg => NONE_msg msg)
   else NONE_msg ("Unknown declaration element type: "++elem_name)
   (* TODO: ??? *)
  | _ => NONE_msg "Unknown JSON format of element"
End

(* Note: Spec states "bit" is shorthand for bit<1> *)
Definition petr4_parse_elements_def:
 petr4_parse_elements json_list arch_pkg_opt =
  FOLDL ( \ res_opt json. case res_opt of
                     | SOME_msg res => petr4_parse_element res json
                     | NONE_msg msg => NONE_msg msg) (SOME_msg ([("bit", p_tau_bit 1)],(0,[]),[],[],[],[],[],[],[],arch_pkg_opt,[])) json_list
End

Definition p4_from_json_def:
(p4_from_json json_parse_result arch_pkg_opt =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
  (* TODO: Debug here by TAKE-ing different parts of the json_list *)
  petr4_parse_elements json_list arch_pkg_opt
 | NONE_msg msg => NONE_msg msg)
End

(*
Definition is_control_pblock_def:
 is_control_pblock pblock =
  case pblock of
  | (pblock_regular pbl_type_parser pars_params b_func_map decl_list inits pars_map tbl_map) => F
  | (pblock_regular pbl_type_control pars_params b_func_map decl_list inits pars_map tbl_map) => T
End
*)

Definition pblock_get_tbl_map_def:
 pblock_get_tbl_map pblock =
  case pblock of
  | (pblock_regular pbl_type pars_params b_func_map decl_list inits pars_map tbl_map) => tbl_map
End

Definition ctrl_from_pblock_map_def:
 ctrl_from_pblock_map pblock_map =
  MAP (\ (k, v). pblock_get_tbl_map v) pblock_map
End

(*********)
(* TESTS *)

(*

(* CURRENT WIP *)

val wip_tm = stringLib.fromMLstring $ TextIO.inputAll $ TextIO.openIn "test-examples/good/action_call_ebpf.json";

val wip_parse_thm = EVAL ``parse (OUTL (lex (p4_preprocess_str (^wip_tm)) ([]:token list))) [] T``;

(* More detailed debugging:
val wip_test_tm = dest_SOME_msg $ rhs $ concl $ EVAL ``p4_from_json_preamble ^(rhs $ concl wip_parse_thm)``;

val wip_package_type_tm = rhs $ concl $ EVAL ``EL 11 ^wip_test_tm``;
val wip_package_inst_tm = rhs $ concl $ EVAL ``EL 15 ^wip_test_tm``;

val wip_obj = optionSyntax.dest_some $ rhs $ concl $ EVAL ``case (^wip_package_inst_tm) of | Array [String elem_name; obj] => SOME obj | _ => NONE``;

val wip_tyenv = ``[("bit",p_tau_bit 1); ("packet_in",p_tau_ext "packet_in");
        ("packet_out",p_tau_ext "packet_out");
        ("CounterArray",p_tau_ext "CounterArray");
        ("array_table",p_tau_ext "array_table");
        ("hash_table",p_tau_ext "hash_table");
        ("ebpfFilter",p_tau_pkg "ebpfFilter");
        ("Headers_t",p_tau_xtl struct_ty_struct [])]``;

val wip_bltymap = ``[("parse",pbl_type_parser,["H"],
         [("packet",d_none,p_tau_ext "packet_in");
          ("headers",d_out,p_tau_par "H")]);
        ("filter",pbl_type_control,["H3"],
         [("headers",d_inout,p_tau_par "H3"); ("accept",d_out,p_tau_bool)])]``;

val wip_ptymap = ``[("ebpfFilter",
         ["parse";
          "filter"])]``;

EVAL ``petr4_parse_top_level_inst (^wip_tyenv, ^wip_bltymap, ^wip_ptymap) ^wip_obj``

EVAL ``json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params"] ^wip_obj``

val wip_args = ``[Array
             [String "Expression";
              Object
                [("tags",Array [String "missing_info"; String ""]);
                 ("value",
                  Array
                    [String "instantiation";
                     Object
                       [("tags",Array [String "missing_info"; String ""]);
                        ("type",
                         Array
                           [String "name";
                            Object
                              [("tags",
                                Array [String "missing_info"; String ""]);
                               ("name",
                                Array
                                  [String "BareName";
                                   Object
                                     [("tags",
                                       Array
                                         [String "missing_info"; String ""]);
                                      ("name",
                                       Object
                                         [("tags",
                                           Array
                                             [String "missing_info";
                                              String ""]);
                                          ("string",String "prs")])]])]]);
                        ("args",Array [])]])]];
           Array
             [String "Expression";
              Object
                [("tags",Array [String "missing_info"; String ""]);
                 ("value",
                  Array
                    [String "instantiation";
                     Object
                       [("tags",Array [String "missing_info"; String ""]);
                        ("type",
                         Array
                           [String "name";
                            Object
                              [("tags",
                                Array [String "missing_info"; String ""]);
                               ("name",
                                Array
                                  [String "BareName";
                                   Object
                                     [("tags",
                                       Array
                                         [String "missing_info"; String ""]);
                                      ("name",
                                       Object
                                         [("tags",
                                           Array
                                             [String "missing_info";
                                              String ""]);
                                          ("string",String "pipe")])]])]]);
                        ("args",Array [])]])]]]``;

EVAL ``petr4_parse_pblock_insts ^wip_args``

*)

val wip_parse_res = rhs $ concl $ EVAL ``p4_from_json ^(rhs $ concl wip_parse_thm) (SOME (arch_ebpf (NONE)))``;


(* SIMPLE FILTER *)

val simple_in_stream = TextIO.openIn "test-examples/filter.json";

val simple_input = TextIO.inputAll simple_in_stream;

val simple_input_tm = stringLib.fromMLstring simple_input;

(*val simple_input_preproc_tm = rhs $ concl $ EVAL ``p4_preprocess_str (^simple_input_tm)``;*)

val simple_lex_thm = EVAL ``lex (p4_preprocess_str (^simple_input_tm)) ([]:token list)``;

val simple_parse_thm = EVAL ``parse (OUTL (lex (p4_preprocess_str (^simple_input_tm)) ([]:token list))) [] T``;

(*
val test_parsed_tm = rhs $ concl simple_parse_thm;
*)

val simple_parse_clean = rhs $ concl $ EVAL ``p4_from_json ^(rhs $ concl simple_parse_thm) NONE``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb simple_parse_clean;


(* VSS *)

val vss_in_stream = TextIO.openIn "test-examples/vss-example.json";

val vss_input = TextIO.inputAll vss_in_stream;

val vss_input_tm = stringLib.fromMLstring vss_input;

(* Lexing: Takes around 40 seconds
val vss_lex_thm = EVAL ``lex (p4_preprocess_str (^vss_input_tm)) ([]:token list)``;
*)

(* Lexing + parsing: Takes around 40 seconds *)
val vss_parse_thm = EVAL ``parse (OUTL (lex (p4_preprocess_str (^vss_input_tm)) ([]:token list))) [] T``;

val vss_parse_clean = rhs $ concl $ EVAL ``p4_from_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val vss_parse_debug1 = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl $ EVAL ``debug_json ^(rhs $ concl vss_parse_thm)``;

val list_elems = fst $ listSyntax.dest_list $ snd $ dest_comb $ rhs $ concl vss_parse_clean;

*)

val _ = export_theory ();
