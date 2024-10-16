open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "petr4_to_hol4p4";

open stringTheory listTheory ASCIInumbersTheory;
open parse_jsonTheory;
open p4Theory p4_auxTheory;

(* For EVAL *)
open ASCIInumbersLib;

(* Finds an element e obeying P in l, then returns a tuple of e and l with e removed *)
Definition FIND_EXTRACT_def:
 FIND_EXTRACT P l =
  INDEX_FIND 0 P l >>=
  \ (j, e). SOME (e, (TAKE j l)++(DROP (j+1) l))
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

(* For passing string lists to print in strings *)
Definition merge_string_list'_def:
 (merge_string_list' [] = "]") /\
 (merge_string_list' (h::(h'::t)) =
  h++("; "++(merge_string_list' (h'::t)))) /\
 (merge_string_list' (h::t) =
  h++(merge_string_list' t))
End
Definition merge_string_list_def:
 merge_string_list string_list = ("["++(merge_string_list' string_list))
End

(* Option datatype with error message for the NONE case *)
Datatype:
 option_msg_t =
    SOME_msg 'a
  | NONE_msg string
End

(* Also with debug term *)
Datatype:
 option_debug_msg_t =
    SOME_dbg 'a
  | NONE_dbg 'b string
End

Definition opt_add_msg_def:
 opt_add_msg msg opt =
  case opt of
  | SOME x => SOME_msg x
  | NONE => NONE_msg msg
End

Definition msg_add_dbg_def:
 msg_add_dbg data opt =
  case opt of
  | SOME_msg x => SOME_dbg x
  | NONE_msg msg => NONE_dbg data msg
End

Definition dbg_remove_def:
 dbg_remove opt =
  case opt of
  | SOME_dbg x => SOME_msg x
  | NONE_dbg data msg => NONE_msg msg
End

Definition opt_msg_bind_def:
 (opt_msg_bind (NONE_msg msg) f f' = NONE_msg $ f' msg) /\
 (opt_msg_bind (SOME_msg x) f f' = f x)
End


(******************)
(* PRE-PROCESSING *)

Definition json_to_string_wrap_def:
 json_to_string_wrap json = (FOLDL (\ str acc. str++acc) []) (json_to_string json)
End

Definition get_error_msg_def:
 get_error_msg msg json = NONE_msg (msg++(json_to_string_wrap json))
End

Definition json_is_null_def:
 json_is_null json =
  case json of
  | Null => T
  | _ => F
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

Definition json_parse_obj'_def:
 (json_parse_obj' [] [] = SOME []) /\
 (json_parse_obj' [] _  = NONE) /\
 (json_parse_obj' _  [] = NONE) /\
 (json_parse_obj' (h2::t2) ((k, v)::t) =
  if k = h2
  then
   json_parse_obj' t2 t >>=
   \vl. SOME (v::vl)
  else NONE)
End

(* Returns a list of the JSON elements that are the
 * values of the members of json iff the keys match
 * the provided list of strings *)
Definition json_parse_obj_def:
 json_parse_obj fields json =
  json_dest_obj json >>=
  json_parse_obj' fields
End

Definition json_parse_arr'_def:
 (json_parse_arr' _  _ [] = NONE) /\
 (json_parse_arr' name f (h::[t]) =
   json_dest_str h >>=
   \s. if s = name then f t else NONE) /\
 (json_parse_arr' _  _ _ = NONE)
End

(* Returns the list of JSONs that is the tail of the list in json iff
 * the first element is a String that matches the provided string.
 * Note that this is not the general format of a JSON array, but rather
 * a specific pattern found in petr4 JSON exports. *)
Definition json_parse_arr_def:
 json_parse_arr name f json =
  json_dest_arr json >>=
  json_parse_arr' name f
End

Definition json_parse_arr_list'_def:
 (json_parse_arr_list' _ [] = NONE) /\
 (json_parse_arr_list' name_f_l (h::t) =
   json_dest_str h >>=
   \s. INDEX_FIND 0 (\name_f. (FST name_f) = s) name_f_l >>=
   \ (i, name_f).
    (* TODO: can t be empty if we're dealing with an error? *)
    (case t of
     | [] =>
      (SND name_f) Null
     | [t'] =>
      (SND name_f) t'
     | _ => NONE))
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

(************************************)
(* PROGRAM TRANSFORMATION CONSTANTS *)

val apply_result_placeholder = “"gen_apply_result"”;
val apply_result_placeholder_varn = “varn_name ^apply_result_placeholder”;

val reserved_globals = “[^apply_result_placeholder_varn]”;


(***********************)
(* HOL4 JSON TO HOL4P4 *)

Definition p4_from_json_preamble:
 p4_from_json_preamble json_parse_result =
  case json_parse_result of
  | INR (json, [], []) =>
   (* petr4: all output is a list with an array at top *)
   (case json_dest_arr json of
   | SOME json_list =>
    (* petr4: first element in this list is the string "program" *)
    (case json_list of
     | (json'::(json_list'::[])) =>
      if json' = String "program"
      then
       (case json_dest_arr json_list' of
        | SOME json_list'' => SOME_msg json_list''
        | _ => NONE_msg "petr4 format error: Top-level List did not have Array as second element")
      else NONE_msg "petr4 format error: Top level List did not have String \"program\" as first element"
     | _ => NONE_msg "petr4 format error: Empty program")
   | NONE => NONE_msg "petr4 format error: JSON was not a singleton list containing an Array at top level")
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

(* Some types which are used throughout the .p4 parser which are not part of the HOL4P4 state or
 * context *)
val _ = type_abbrev("tyenv", ``:(string, p_tau) alist``);
val _ = type_abbrev("enummap", ``:(string # (string, v) alist) list``);
val _ = type_abbrev("ftymap", ``:((funn, (p_tau list # p_tau)) alist)``);

(* pblock and tbl_map with list of actions stored *)
val _ = type_abbrev("tbl_map_extra", ``:((string, ((mk list) # x_list # (x # e_list))) alist)``);
val _ = type_abbrev("pblock_extra", ``:(pbl_type # ((string # d) list) # b_func_map # t_scope # pars_map # tbl_map_extra)``);

(* The tau signifies the type argument(s) *)
Datatype:
 vss_pkg_t =
  vss_pkg_VSS tau
End

Datatype:
 ebpf_pkg_t =
  ebpf_pkg_ebpfFilter tau
End

Datatype:
 v1model_pkg_t =
  v1model_pkg_V1Switch tau tau
End

(* The option type signifies whether the top-level package has been recognized yet *)
Datatype:
 arch_t =
    arch_vss (vss_pkg_t option)
  | arch_ebpf (ebpf_pkg_t option)
  | arch_v1model (v1model_pkg_t option)
End


(********************)
(* Type definitions *)

Definition petr4_parse_width_def:
 petr4_parse_width json_list =
  case json_list of
  | (width::(null::[])) =>
   json_dest_str width >>=
   \width_res.
    if json_is_null null
    then
     fromDecString width_res >>=
     \w_num. SOME (p_tau_bit w_num)
    else NONE
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

(* Different one-off format for switch cases *)
Definition petr4_parse_case_name_def:
 petr4_parse_case_name case_name =
  json_parse_arr "name" SOME case_name >>=
  \name_obj.
   (case json_parse_obj ["tags"; "name"] name_obj of
    | SOME [tags'; name'] =>
     (case json_parse_obj ["tags"; "string"] name' of
      | SOME [tags''; name''] =>
       json_dest_str name''
      | _ => NONE)
    | _ => NONE)
End

Definition petr4_parse_names_def:
 (petr4_parse_names [] = SOME []) /\
 (petr4_parse_names (h::t) =
   petr4_parse_name h >>=
   \res_hd. petr4_parse_names t >>=
   \res_tl. SOME (res_hd::res_tl))
End

Definition petr4_parse_bare_name_def:
 petr4_parse_bare_name bname =
  json_parse_arr "BareName" SOME bname >>=
  \bname_obj.
   (case json_parse_obj ["tags"; "name"] bname_obj of
    | SOME [tags; name] => petr4_parse_name name
    | _ => NONE)
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
   json_parse_arr_list
     [("name", petr4_parse_tyname);
      ("specialized", \json'.
                       (case json_parse_obj ["tags"; "base"; "args"] json' of
                        | SOME [tags; base; args] =>
                         (json_parse_arr "name" petr4_parse_tyname base)
                        | _ => NONE));] json
End

Definition petr4_num_binop_lookup_def:
 petr4_num_binop_lookup optype (op1, op2) =
  ALOOKUP [("Plus", op1 + op2);
           ("Minus", op1 - op2);
           ("Mul", op1 * op2);
           ("Div", op1 DIV op2);
           ("Mod", op1 MOD op2)] optype
End

Triviality get_error_msg_distinct:
 !str obj str'. get_error_msg str obj <> SOME_msg str'
Proof
fs[get_error_msg_def]
QED

Triviality json_parse_arr_size:
 !str json json'.
 json_parse_arr str SOME json = SOME json' ==>
 json_size json' < json_size json
Proof
rpt strip_tac >>
fs[json_parse_arr_def, app_opt_def] >>
Cases_on ‘json’ >> (fs[json_dest_arr_def]) >>
rw[] >>
Cases_on ‘l’ >> (fs[json_parse_arr'_def]) >>
Cases_on ‘t’ >> (fs[json_parse_arr'_def]) >>
Cases_on ‘t'’ >> (fs[json_parse_arr'_def, json_size_def, app_opt_def])
QED

Triviality json_parse_obj_size:
 !str_list json json_list.
 json_parse_obj str_list json = SOME json_list ==>
 json3_size json_list < json_size json
Proof
Induct_on ‘json_list’ >- (
 rpt strip_tac >>
 fs[json_parse_obj_def, json_dest_obj_def, app_opt_def] >>
 Cases_on ‘json’ >> (fs[json_size_def])
) >>
rpt strip_tac >>
fs[json_parse_obj_def, app_opt_def] >>
Cases_on ‘json’ >> (fs[json_dest_obj_def]) >>
rw[] >>
Cases_on ‘str_list’ >> (fs[json_parse_obj'_def, json_size_def]) >>
(Cases_on ‘l’ >> (fs[json_parse_obj'_def, json_size_def])) >>

Cases_on ‘h''’ >> (fs[json_parse_obj'_def, json_size_def, app_opt_def]) >>
Cases_on ‘json_parse_obj' t t'’ >> (fs[json_parse_obj'_def, json_size_def]) >>
rw[] >>
subgoal ‘(case (Object t') of
                Object obj => SOME obj
              | Array v8 => NONE
              | String v9 => NONE
              | Number v10 v11 v12 => NONE
              | Bool v13 => NONE
              | Null => NONE) =
             SOME t'’ >- (
 fs[]
) >>
subgoal ‘json3_size json_list < json_size (Object t')’ >- (
 metis_tac[]
) >>
fs[json_size_def]
QED

(* Parses compile-time known constants, e.g. in bitstring widths *)
(* TODO: Should the return type be option_msg?  *)
Definition petr4_parse_compiletime_constantexp_def:
 petr4_parse_compiletime_constantexp exp =
  case json_dest_arr exp of
  | SOME [exptype_str; x_obj] =>
   json_dest_str exptype_str >>=
   \exptype.
    if exptype = "int"
    then
     (case json_parse_obj ["tags"; "x"] x_obj of
      | SOME [tags; x] =>
       (case json_parse_obj ["tags"; "value"; "width_signed"] x of
        | SOME [tags'; value_str; width_signed] =>
         json_dest_str value_str >>=
         \value.
          (case width_signed of
           | Null => fromDecString value
           (* TODO: Not sure if this can happen here... *)
           | Array [Number (Positive, width) NONE NONE; Bool F] =>
            fromDecString value
           | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    else if exptype = "binary_op"
    then (* Binary operation *)
     (case json_parse_obj ["tags"; "op"; "args"] x_obj of
      | SOME [tags; op; args] =>
       (case json_dest_arr op of
        | SOME [optype_str; op_tags] =>
         json_dest_str optype_str >>=
         \optype.
          (case json_dest_arr args of
           | SOME [op1; op2] =>
            petr4_parse_compiletime_constantexp op1 >>=
            \res_op1. petr4_parse_compiletime_constantexp op2 >>=
             (* TODO: Treat comparisons, bit shift+concat and regular binops differently *)
             \res_op2. petr4_num_binop_lookup optype (res_op1, res_op2)
           | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    else NONE
  | _ => NONE
Termination
WF_REL_TAC `measure json_size` >>
rpt strip_tac >> (
 Cases_on ‘exp’ >> (fs[json_dest_arr_def, json_size_def]) >>
 Cases_on ‘op’ >> (fs[]) >>
 Cases_on ‘args’ >> (fs[]) >>
 rw[] >>
 imp_res_tac json_parse_obj_size >>
 fs[json_size_def]
)
End

(* TODO: Expand as you encounter more types *)
(* If type specialisation is ignored via "ignore_tyspec", type-specialised types
 * will be treated as their base type: this will result in p_tau_par.
 * This is used e.g. when parsing package types, when only the base type of the
 * parameter is relevant.
 * Since type-parameterised extern types are currently not treated, all extern
 * types will be plain. *)
Definition petr4_parse_ptype_def:
 petr4_parse_ptype ignore_tyspec tyenv json =
  json_parse_arr_list
   [("bit", \json'.
             (case json_parse_obj ["tags"; "expr"] json' of
              | SOME [tags; expr] =>
               petr4_parse_compiletime_constantexp expr >>=
               \n. SOME (p_tau_bit n)
              | _ => NONE));
    ("bool", \json'. SOME p_tau_bool);
    ("error", \json'. SOME (p_tau_bit 32));
    ("void", \json'. SOME p_tau_bot);
    ("name", \json'. petr4_parse_tyname json' >>=
                     (\name. case ALOOKUP tyenv name of
                      | SOME p_tau => SOME p_tau
                      | NONE => SOME (p_tau_par name)));
    (* Note. It's OK to map the string type to p_tau_bot, since we never want to
     * do type inference in expressions of this type. *)
    ("string", \json'. SOME p_tau_bot);
    ("specialized", \json'.
                     (case json_parse_obj ["tags"; "base"; "args"] json' of
                      | SOME [tags; base; args] =>
                       petr4_parse_type_name base >>=
                       \name.
                        (case ALOOKUP tyenv name of
                         | SOME (p_tau_ext ext_name) =>
                          SOME (p_tau_ext ext_name)
                         | _ =>
                          if ignore_tyspec
                          then SOME (p_tau_par name)
                          else NONE)
                      | _ => NONE))] json
End

(* Version for non-parameterized types *)
Definition petr4_parse_type_def:
 petr4_parse_type tyenv json =
  petr4_parse_ptype F tyenv json >>=
  \p_tau. deparameterise_tau p_tau
End

(* TODO: Avoid explicit case matching on list possible? *)
Definition petr4_typedef_to_tyenvupdate_def:
 petr4_typedef_to_tyenvupdate tyenv json =
  case json_parse_obj ["tags"; "annotations"; "name"; "typ_or_decl"] json of
  | SOME [tags; annot; ty_name; typ_or_decl] =>
   opt_pair
    (petr4_parse_name ty_name)
    (json_parse_arr "Left" SOME typ_or_decl >>=
     petr4_parse_ptype F tyenv)
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
      (case ALOOKUP enummap enum_name of
       | SOME enum_mem_map =>
        SOME (AUPDATE enummap (enum_name,
              AUPDATE_LIST enum_mem_map (ZIP (enum_members,
                                              MAP get_32bitv (COUNT_LIST_interval (LENGTH enum_mem_map) (LENGTH enum_members))))))
       | NONE =>
        SOME (AUPDATE enummap (enum_name,
              AUPDATE_LIST [] (ZIP (enum_members,
                                    MAP get_32bitv (COUNT_LIST_interval 0 (LENGTH enum_members)))))))
     | NONE => NONE)
   else if (ALOOKUP enummap enum_name = NONE)
   then
    (case petr4_parse_names members of
     | SOME enum_members =>
      SOME (AUPDATE enummap (enum_name,
             AUPDATE_LIST [] (ZIP (enum_members,
                                   MAP get_32bitv (COUNT_LIST_interval 0 (LENGTH enum_members))))))
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
    | SOME enummap' => SOME_msg enummap'
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

Definition n_of_e_bitv_def:
 n_of_e_bitv e =
  case e of
  | (e_v v) =>
   (case v of
    | (v_bit (bl, n)) =>
     SOME (v2n bl)
    | _ => NONE)
  | _ => NONE
End

(* TODO: More types of expressions *)
(* TODO: vtymap uses varn_name to later use varn_star for case of function call *)
Definition exp_to_p_tau_def:
 exp_to_p_tau (vtymap, ftymap) exp =
  case exp of
  | (e_v $ v_bool b) => SOME p_tau_bool
  | (e_v (v_bit (bl, n))) => SOME (p_tau_bit n)
  | (e_acc struct fld) =>
   (case exp_to_p_tau (vtymap, ftymap) struct of
    | SOME (p_tau_xtl struct_ty f_t_list) =>
     (FIND (\ (f, t). f = fld)  f_t_list) >>=
      \ (fld, res_tau). SOME res_tau
    | _ => NONE)
  | (e_var (varn_name varname)) => ALOOKUP vtymap (varn_name varname)
  | (e_binop op1 binop op2) => exp_to_p_tau (vtymap, ftymap) op1
  | (e_slice e hi lo) =>
   n_of_e_bitv hi >>=
   \n. n_of_e_bitv lo >>=
   \n'. SOME (p_tau_bit ((n - n') + 1))
  | (e_call funn e_l) =>
   (* Lookahead exception: second arg is dummy type argument *)
   if funn = (funn_ext "packet_in" "lookahead")
   then
    (case e_l of
     | [e1;e2] => exp_to_p_tau (vtymap, ftymap) e2
     | _ => NONE)
   else
    (ALOOKUP ftymap funn >>=
     \ftys. SOME $ SND ftys)
  | _ => NONE
End

(* TODO: Use list option monad *)
Definition exps_to_p_taus_def:
 (exps_to_p_taus (vtymap, ftymap) [] = SOME []) /\
 (exps_to_p_taus (vtymap, ftymap) (h::t) = 
  exp_to_p_tau (vtymap, ftymap) h >>=
  \p_tau. exps_to_p_taus (vtymap, ftymap) t >>=
  \res. SOME (p_tau::res))
End

Definition exp_to_funn_def:
 exp_to_funn (vtymap, extfun_list) exp =
  case exp of
  (* Regular function call *)
  | (e_var (varn_name name)) =>
   if MEM name extfun_list
   then SOME (SOME (funn_ext "" name), NONE)
   else SOME (SOME (funn_name name), NONE)
  (* Extern method call/validity manipulation *)
  | (e_acc obj fun_name) =>
     (* TODO: This is a hack, making exceptions for validity manipulations and "apply"...
      *       Need to check type of obj to see what methods exist *)
   (if fun_name = "isValid" then
     SOME (SOME (funn_ext "header" "isValid"), SOME obj)
    else if fun_name = "setInvalid" then
     SOME (SOME (funn_ext "header" "setInvalid"), SOME obj)
    else if fun_name = "setValid" then
     SOME (SOME (funn_ext "header" "setValid"), SOME obj)
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
   tyu_l_only t >>=
   \l. SOME (a::l)
  | _ => NONE)
End

Definition petr4_unop_lookup_def:
 petr4_unop_lookup unop_str = 
  ALOOKUP [("Not", unop_neg);
           ("BitNot", unop_compl);
           ("UMinus", unop_neg_signed)] unop_str
End

(* TODO: Annoying special treatment of concat... *)
Definition petr4_binop_lookup_def:
 petr4_binop_lookup binop_str =   
   if binop_str = "PlusPlus"
   then SOME ( \op1 op2. (e_concat op1 op2))
   else
    case
     (ALOOKUP [("Plus", binop_add);
               ("PlusSat", binop_sat_add);
               ("Minus", binop_sub);
               ("MinusSat", binop_sat_sub);
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
               ("Or", binop_bin_or)] binop_str) of
     | SOME binop => SOME ( \op1 op2. (e_binop op1 binop op2))
     | NONE => NONE
End

(* Like ALOOKUP, but also requires the number of arguments to match
 * Required due to overloaded function names, e.g. extract in packet_in *)
(* TODO: Should this really return a tuple and not only the args? Check where this is used... *)
Definition find_fty_match_args_def:
 find_fty_match_args (ftymap:ftymap) funn numargs =
   (case FIND (\ (funn', (tyargs', tyret')). if funn = funn' then (numargs = LENGTH tyargs') else F) ftymap of
    | SOME fty => SOME (SND fty)
    | NONE => NONE)
End

Triviality find_fty_match_args_LENGTH:
!ftymap funn numargs res.
 find_fty_match_args ftymap funn numargs = SOME res ==>
 LENGTH (FST res) = numargs
Proof
fs[find_fty_match_args_def] >>
rpt strip_tac >>
fs[FIND_def] >>
Cases_on ‘(INDEX_FIND 0
                (\(funn',tyargs',tyret').
                     funn = funn' /\ numargs = LENGTH tyargs') ftymap)’ >> (fs[]) >- (
Cases_on ‘x’ >>
imp_res_tac index_find_first >>
PairCases_on ‘r’ >>
gvs[]
)
QED

Definition json_p_tau_opt_list_size_def:
 json_p_tau_opt_list_size json_p_tau_opt_list =
  let (json_list, p_tau_opt_list) = UNZIP json_p_tau_opt_list in
   json3_size json_list
End

Datatype:
 exp_res_t =
    Number num
  | Exp e
  (* table.apply().action_run expression to be inlined *)
  | InlineApp (string list) e
End

Definition msg_opt_INL_def:
 (msg_opt_INL (SOME_msg (e:e)) = (SOME_msg ((INL e):(e + num)))) /\
 (msg_opt_INL (NONE_msg msg) = (NONE_msg msg))
End

(* This gathers all known extern functions which have type arguments that don't appear
 * among their arguments. *)
(* TODO: This is architecture-dependent in general... *)
Definition incomplete_typeinf_def:
 incomplete_typeinf funn =
  case funn of
  | (funn_ext ext_obj ext_fun) =>
   (if ext_obj = "packet_in" /\  ext_fun = "lookahead"
    then T
    else F)
  | _ => F
End

Definition get_typeinf_dummy_args_def:
 get_typeinf_dummy_args tyenv tyargs =
  case
   FOLDL ( \ args_opt tyarg.
          case args_opt of
          | SOME args =>
           petr4_parse_type tyenv tyarg >>=
           \type. SOME (args++[(e_v $ arb_from_tau type)])
          | NONE => NONE) (SOME []) tyargs of
   | SOME dummy_args => SOME_msg dummy_args
   | NONE => get_error_msg "could not transform extern function's type arguments to dummy arguments: " (Array tyargs)
End

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
Definition petr4_parse_expression_gen_def:
(petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) =
  case exp of
  (* TODO: Null can occur in case of return without value - works generally? *)
  | Null => SOME_msg (Exp (e_v v_bot))
  (* True and false *)
  | Array [String "true";
     Object [("tags", tags)]] =>
   SOME_msg (Exp (e_v (v_bool T)))
  | Array [String "false";
     Object [("tags", tags)]] =>
   SOME_msg (Exp (e_v (v_bool F)))
  (* Struct member/field access *)
  | Array [String "expression_member";
     Object [("tags", tags);
             ("expr", nested_exp);
             ("name", name)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (nested_exp, NONE) of
    | SOME_msg (Exp mem_nested_exp) =>
     (case petr4_parse_name name of
      | SOME mem_name =>
       SOME_msg (Exp (e_acc mem_nested_exp mem_name))
      | NONE => get_error_msg "could not parse name: " name)
    (* Nested apply expression allowed for struct field access (action_run, et.c.)*)
    | SOME_msg (InlineApp str_l e_app) =>
     (case petr4_parse_name name of
      | SOME mem_name =>
       SOME_msg (InlineApp str_l (e_acc e_app mem_name))
      | NONE => get_error_msg "could not parse name: " name)
    | SOME_msg (Number n) => NONE_msg "cannot access field of constant"
    | NONE_msg mem_msg => NONE_msg mem_msg)
  (* Variable *)
  | Array [String "name";
           name] =>
   (case petr4_parse_tyname name of
    | SOME var_name =>
     let varn = (varn_name var_name) in
     (* If variable is multiply defined in vtymap, this occurrence is not referring
      * to a global constant *)
     if (LENGTH $ FILTER (\ (varn', ty). varn' = varn) vtymap) > 1
     then SOME_msg (Exp (e_var varn))
     else
      (case ALOOKUP gscope varn of
       | SOME (v, lval_opt) =>
        SOME_msg (Exp (e_v v))
       (* Not in gscope ==> not a global constant *)
       | NONE => SOME_msg (Exp (e_var varn)))
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
            | SOME n => SOME_msg (Exp (e_v (v_bit (fixwidth w (n2v n), w))))
            | NONE => NONE_msg ("could not parse string to integer: "++value_str))
          | NONE =>
           (case fromDecString value_str of
            | SOME n => SOME_msg (Number n)
            | NONE => NONE_msg ("could not parse string to integer after failing to obtain width of expression type: "++value_str)))
        | NONE =>
         (case fromDecString value_str of
          | SOME n => SOME_msg (Number n)
          | NONE => NONE_msg ("could not parse string to integer: "++value_str)))
      | Array [Number (Positive, width) NONE NONE; Bool F] =>
       (case fromDecString value_str of
        | SOME n =>
         (let bl = n2v n in
          if LENGTH bl > width then NONE_msg ("integer overflows width: "++value_str)
          else SOME_msg (Exp (e_v (v_bit (fixwidth width bl, width)))))
        | NONE => NONE_msg ("could not parse string to integer: "++value_str))
      | _ => get_error_msg "unsupported integer type: " width_signed)
    | _ => get_error_msg "could not obtain value and width of integer literal: " x)
  (* Cast *)
  | Array [String "cast";
     Object [("tags", tags);
             ("type", cast_type);
             ("expr", op)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (op, NONE) of
    | SOME_msg res_op =>
     (case petr4_parse_type tyenv cast_type of
      | SOME (tau_bit n) =>
       (case res_op of
        | Exp op_exp =>
         SOME_msg (Exp (e_cast (cast_unsigned n) op_exp))
        | Number op_const =>
         SOME_msg (Exp (e_v (v_bit (fixwidth n (n2v op_const), n))))
        | InlineApp s_l app_exp =>
         get_error_msg "apply expression unsupported for unops: " op)
      | SOME _ => get_error_msg "unsupported cast type: " cast_type
      | NONE => get_error_msg "unknown cast type: " cast_type)
    | NONE_msg op_msg => NONE_msg op_msg)
  (* Unary operation *)
  | Array [String "unary_op";
     Object [("tags", tags);
             ("op", Array [String optype; op_tags]);
             ("arg", op)]] =>
   (* TODO: All unary operations preserve type? *)
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (op, p_tau_opt) of
    | SOME_msg res_op =>
     (case petr4_unop_lookup optype of
      | SOME unop =>
       (case res_op of
        | Exp op_exp =>
         SOME_msg (Exp (e_unop unop op_exp))
        | _ =>
         (* TODO: Infer type directly from tau_opt *)
         get_error_msg "type inference or apply expression unsupported for unops: " exp)
      | NONE => NONE_msg ("unknown optype: "++optype))
    | NONE_msg op_msg => NONE_msg op_msg)
  (* Binary operation *)
  | Array [String "binary_op";
     Object [("tags", tags);
             ("op", Array [String optype; op_tags]);
             ("args", Array [op1; op2])]] =>
   (case petr4_binop_lookup optype of
    | SOME mk_binop =>
     let p_tau_opt_left = if MEM optype ["Plus"; "PlusSat"; "Minus"; "MinusSat"; "Mul"; "Shl"; "Shr"; "BitAnd"; "BitXor"; "BitOr"] then p_tau_opt else NONE in
     let p_tau_opt_right = if MEM optype ["Plus"; "PlusSat"; "Minus"; "MinusSat"; "Mul"; "BitAnd"; "BitXor"; "BitOr"] then p_tau_opt else NONE in
     (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (op1, p_tau_opt_left) of
      | SOME_msg res_op1 =>
       (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (op2, p_tau_opt_right) of
        | SOME_msg res_op2 =>
         (* TODO: Double-check this type inference works as intended in all cases *)
         (case (res_op1, res_op2) of
          | (Exp op1_exp, Exp op2_exp) => SOME_msg (Exp (mk_binop op1_exp op2_exp))
          | (Exp op1_exp, Number op2_const) =>
           (case exp_to_p_tau (vtymap, ftymap) op1_exp of
            | SOME (p_tau_bit n) =>
             SOME_msg (Exp (mk_binop op1_exp (e_v (v_bit (fixwidth n (n2v op2_const), n)))))
            | SOME _ => get_error_msg "non-bitstring type inference unsupported for expression: " exp
            | NONE => get_error_msg "type inference failed for expression: " exp)
          | (Number op1_const, Exp op2_exp) =>
           (case exp_to_p_tau (vtymap, ftymap) op2_exp of
            | SOME (p_tau_bit n) =>
             SOME_msg (Exp (mk_binop (e_v (v_bit (fixwidth n (n2v op1_const), n))) op2_exp))
            | SOME _ => get_error_msg "non-bitstring type inference unsupported for expression: " exp
            | NONE => get_error_msg "type inference failed for expression: " exp)
          | _ => get_error_msg "expression contains binop on constants or apply exp: " exp)
        | NONE_msg op2_msg => NONE_msg op2_msg)
      | NONE_msg op1_msg => NONE_msg op1_msg)
    | NONE => NONE_msg ("unknown optype: "++optype))
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
       (case ALOOKUP enummap enum_type_name of
        | SOME enum_type_map =>
         (case ALOOKUP enum_type_map enum_field_name of
          | SOME enum_val =>
           SOME_msg (Exp (e_v enum_val))
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
     (case ALOOKUP enummap "error" of
      | SOME error_map =>
       (case ALOOKUP error_map error_name of
        | SOME error_val =>
         SOME_msg (Exp (e_v error_val))
        | NONE => NONE_msg "")
      | NONE => NONE_msg "enumeration type map does not contain the error type.")
    | NONE => get_error_msg "could not parse name: " name)
  (* Function call *)
  (* Note extra arguments for actions (when used to parse actions in tables) added later *)
  | Array [String "call";
           Object [("tags", tags);
                   ("func", func_name);
                   ("type_args", Array tyargs);
                   ("args", Array args)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (func_name, NONE) of
    | SOME_msg (Exp res_func_name) =>
     (case exp_to_funn (vtymap, extfun_list) res_func_name of
      | SOME (SOME res_func_name', NONE) =>
       (case find_fty_match_args ftymap res_func_name' (LENGTH args) of
        | SOME (arg_tys, ret_ty) =>
         (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME arg_tys)) of
          | SOME_msg res_args =>
           (* TODO: Here, check if function's arguments has incomplete type information.
            * If so, parse tyargs to types, then create a dummy values for them and pass as arguments *)
           if incomplete_typeinf res_func_name'
           then
            (case get_typeinf_dummy_args tyenv tyargs of
             | SOME_msg dummy_args =>
              SOME_msg (Exp (e_call res_func_name' (res_args++dummy_args)))
             | NONE_msg dummy_msg => NONE_msg ("could not parse function call type arguments: "++dummy_msg))
           else
            SOME_msg (Exp (e_call res_func_name' res_args))
          | NONE_msg func_name_msg => NONE_msg ("could not parse function call arguments: "++func_name_msg))
        | NONE => get_error_msg "could not retrieve type of function: " func_name)
      (* Apply expressions are inlined: replaced with a temporary variable with table's name in
       * expression, prepended by apply statement + assignment to table variable *)
      | SOME (NONE, SOME table_exp) =>
       (* Get name from table *)
       (case table_exp of
        | (e_var (varn_name tbl_name)) =>
         SOME_msg (InlineApp [tbl_name] (e_var (varn_name tbl_name)))
        | _ => get_error_msg "could not parse table name: " func_name)
      (* Extern method calls. Also, validity manipulation is modeled in HOL4P4 as a
       * method call *)
      | SOME (SOME ext_method, SOME ext_arg) =>
      (* TODO: Do type inference for method calls *)
(*
       (case find_fty_match_args ftymap ext_method (LENGTH args) of
        | SOME (arg_tys, ret_ty) =>
*)
         (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, REPLICATE (LENGTH args) NONE)) of
          | SOME_msg res_args =>
           (* TODO: Here, check if function's arguments has incomplete type information.
            * If so, parse tyargs to types, then create a dummy values for them and pass as arguments *)
           if incomplete_typeinf ext_method
           then
            (case get_typeinf_dummy_args tyenv tyargs of
             | SOME_msg dummy_args =>
              SOME_msg (Exp (e_call ext_method (([ext_arg]++res_args)++dummy_args)))
             | NONE_msg dummy_msg => NONE_msg ("could not parse method call type arguments: "++dummy_msg))
           else
            SOME_msg (Exp (e_call ext_method ([ext_arg]++res_args)))
          | NONE_msg func_name_msg => NONE_msg ("could not parse method call arguments: "++func_name_msg))
(*
        | NONE => get_error_msg "could not retrieve type of method call: " func_name)
*)
      | _ => get_error_msg "could not parse called function name: " func_name)
    | _ => get_error_msg "unknown format of called function name: " func_name)
  (* Bit slice *)
  | Array [String "bit_string_access";
           Object [("tags", tags);
                   ("bits", bits);
                   ("lo", lo);
                   ("hi", hi)]] =>
   (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (bits, NONE) of
    | SOME_msg (Exp bits_exp) =>
     (case petr4_parse_compiletime_constantexp lo of
      | SOME lo_n =>
       (case petr4_parse_compiletime_constantexp hi of
        | SOME hi_n =>
         (* TODO: Hard-coded to width 16 here, this could be just nums instead *)
         SOME_msg (Exp (e_slice bits_exp (e_v $ v_bit (w16 (n2w hi_n))) (e_v $ v_bit (w16 (n2w lo_n)))))
        | NONE => get_error_msg "could not parse compile-time constant: " hi)
      | NONE => get_error_msg "could not parse compile-time constant: " lo)
    | _ => get_error_msg "unknown format of bit-slice: " bits)
  (* Tuple *)
  | Array [String "list";
           Object [("tags", tags);
                   ("values", Array exp_list)]] =>
   (case petr4_parse_expressions (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP(exp_list, REPLICATE (LENGTH exp_list) NONE)) of
    | SOME_msg exp_list_res =>
     SOME_msg (Exp (e_struct (ZIP(MAP toString $ TL $ COUNT_LIST ((LENGTH exp_list_res) + 1), exp_list_res))))
    | NONE_msg exps_msg => NONE_msg ("could not parse tuple element: "++exps_msg))
  | _ => get_error_msg "unknown JSON format of expression: " exp) /\
(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
 (petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) [] =
  SOME_msg []) /\
 (petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (h::t) =
  case h of
  | (Array [String argtype; Object [("tags", tags); ("value", exp)]], p_tau_opt) =>
   if argtype = "Expression" then
    case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) of
     | SOME_msg (Exp exp_res) =>
      (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
       | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
       | NONE_msg exps_msg => NONE_msg exps_msg)
     | SOME_msg (Number c) =>
      (case p_tau_opt of
       | SOME (p_tau_bit n) =>
        (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
         | SOME_msg exps_res => SOME_msg ((e_v (v_bit (fixwidth n (n2v c), n)))::exps_res)
         | NONE_msg exps_msg => NONE_msg exps_msg)
       | SOME other_tau => get_error_msg "non-bitstring type inference unsupported for exp: " exp
       | NONE => get_error_msg "type inference information missing for function argument: " exp)
     | SOME_msg (InlineApp s_l exp_app) => get_error_msg "apply expressions as arguments disallowed by import tool: " exp
     | NONE_msg exp_msg => NONE_msg ("could not parse arguments: "++exp_msg)
   else NONE_msg ("unsupported argument type: "++argtype)
  | _ => get_error_msg "unknown JSON format of argument: " (FST h)) /\
 (petr4_parse_expressions (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) [] =
  SOME_msg []) /\
 (petr4_parse_expressions (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) ((h1, h2)::t) =
  case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (h1, h2) of
  | SOME_msg (Number n) => get_error_msg "no type inference information provided for integer constant: " h1
  | SOME_msg (InlineApp s_l e) => get_error_msg "apply expression in unsupported location: " h1
  | SOME_msg (Exp exp_res) =>
    (case petr4_parse_expressions (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
     | SOME_msg exps_res => SOME_msg (exp_res::exps_res)
     | NONE_msg exps_msg => NONE_msg exps_msg)
   | NONE_msg exp_msg => NONE_msg ("could not parse expression: "++exp_msg))
Termination
WF_REL_TAC `measure ( \ t. case t of
                           | (INL (maps, json, p_tau_opt)) => json_size json
                           | (INR $ INL (maps, json_list)) => json_p_tau_opt_list_size json_list
                           | (INR $ INR (maps, json_list)) => json_p_tau_opt_list_size json_list)` >>
fs[json_p_tau_opt_list_size_def] >>
rpt strip_tac >> (fs[json_size_def]) >- (
 subgoal ‘?l1 l2. UNZIP t = (l1, l2)’ >- (fs[UNZIP_MAP]) >>
 fs []
) >- (
 subgoal ‘?l1 l2. UNZIP t = (l1, l2)’ >- (fs[UNZIP_MAP]) >>
 fs []
) >- (
 subgoal ‘?l1 l2. UNZIP t = (l1, l2)’ >- (fs[UNZIP_MAP]) >>
 fs []
) >- (
 subgoal ‘LENGTH args = LENGTH p_1'5'’ >- (imp_res_tac find_fty_match_args_LENGTH >> fs[]) >>
 fs[listTheory.UNZIP_ZIP]
)
End

(* TODO: Baking this into the above messes up the termination proof... *)
Definition petr4_parse_expression_def:
 petr4_parse_expression (tyenv, enummap:enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) =
  case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) of
  | SOME_msg (Number n) => get_error_msg "no type inference information provided for integer constant: " exp
  | SOME_msg (Exp e) => SOME_msg e
  | SOME_msg (InlineApp s_l e) => get_error_msg "apply expression in unsupported location: " exp
  | NONE_msg exp_msg => NONE_msg ("could not parse value: "++exp_msg)
End

(* "Mini big-step semantics" *)
(* TODO: Move somewhere? This could maybe be useful... *)
Definition exp_to_val_def:
 exp_to_val gscope exp =
  case exp of
  | (e_v val) => SOME val
  | (e_var var) =>
   (* Note that exp_to_val is only used for compile-time-known constants.
    * These should also already have been treated by petr4_parse_expression_gen *)
   (case ALOOKUP gscope var of
    | SOME (v, lval_opt) =>
     SOME v
    | NONE => NONE)
  | (e_binop e1 binop e2) =>
   (case exp_to_val gscope e1 of
    | SOME (v_bit bitv) =>
     (case exp_to_val gscope e2 of
      | SOME (v_bit bitv') =>
       (case bitv_binop binop bitv bitv' of
        | SOME bitv'' => SOME (v_bit bitv'')
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | (e_cast (cast_unsigned m) e) =>
   (case exp_to_val gscope e of
    | SOME (v_bit bitv) => SOME (v_bit (bitv_cast m bitv))
    | SOME (v_bool b) => SOME (v_bit (bool_cast m b))
    | _ => NONE)
  | _ => NONE
End

(* NOTE: Should vtymap be needed at top level?
 *       Remove tyenv, doesn't seem to be needed? *)
(* TODO: Merge with petr4_parse_compiletime_constantexp? *)
Definition petr4_parse_value_def:
 petr4_parse_value (tyenv, enummap:enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) =
  case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, p_tau_opt) of
  | SOME_msg (Exp res_exp) =>
   (case exp_to_val gscope res_exp of
    | SOME val => SOME_msg val
    | NONE => get_error_msg "expression could not be parsed as value: " exp)
  | SOME_msg _ => get_error_msg "type inference failed for integer constant: " exp
  | NONE_msg exp_msg => NONE_msg ("could not parse value: "++exp_msg)
End

(*************)
(* Constants *)

(* TODO: Tau not used for any check? *)
Definition petr4_constant_to_scopeupdate_def:
 petr4_constant_to_scopeupdate (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) json =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"; "value"] json of
  | SOME [tags; annot; json_type; name; json_value] =>
   (case petr4_parse_ptype F tyenv json_type of
    | SOME p_tau =>
     (case petr4_parse_name name of
      | SOME c_name =>
       (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (json_value, SOME p_tau) of
        | SOME_msg value => SOME_msg (varn_name c_name, value)
        | NONE_msg val_msg => NONE_msg val_msg)
      | NONE => get_error_msg "could not parse name: " name)
    | NONE => get_error_msg "could not parse type: " json_type)
  | _ => get_error_msg "unknown JSON format of constant: " json
End

(* This is used to parse global constants *)
Definition petr4_parse_constant_def:
 petr4_parse_constant (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) constant =
  case petr4_constant_to_scopeupdate (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) constant of
   | SOME_msg (varn, val) =>
    if ~(MEM varn ^reserved_globals)
    then
     (case v_to_tau val of
      | SOME tau =>
       SOME_msg ((varn, parameterise_tau tau)::vtymap, AUPDATE gscope (varn, val, NONE))
      | NONE => get_error_msg "unsupported type of constant: " constant)
    else get_error_msg "global constant has name reserved by HOL4P4: " constant
   | NONE_msg const_msg => NONE_msg ("Could not parse constant: "++const_msg) (* TODO: Print constant name using nested msg *)
End

(**********************)
(* Serializable enums *)

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
(* TODO: Remove superfluous parameters *)
Definition petr4_parse_serialization_def:
 (petr4_parse_serialization (tyenv, enummap:enummap, vtymap, gscope:g_scope) expected_tau [] = SOME_msg []) /\
 (petr4_parse_serialization (tyenv, enummap, vtymap, gscope) expected_tau (h::t) =
  case h of
  | Array [name; exp] =>
   (case petr4_parse_name name of
    | SOME mem_name =>
     (* Note serialization values may be compile-time known constants in general *)
     (case petr4_parse_value (tyenv, enummap, vtymap, []:ftymap, gscope, []) (exp, SOME expected_tau) of
       | SOME_msg val_res =>
        (case petr4_parse_serialization (tyenv, enummap, vtymap, gscope) expected_tau t of
         | SOME_msg serialization_res => SOME_msg ((mem_name, val_res)::serialization_res)
         | NONE_msg serialization_msg => NONE_msg serialization_msg)
       | NONE_msg exp_msg => NONE_msg ("could not parse serialization type member value: "++exp_msg))
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown JSON format of serialization type member: " h)
End

Definition petr4_parse_serializable_enum_def:
 petr4_parse_serializable_enum (tyenv, enummap, vtymap, gscope) json =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"; "members"] json of
  | SOME [tags; annot; type; name; Array members] =>
   (case petr4_parse_ptype F tyenv type of
    | SOME enum_type =>
     (case petr4_parse_name name of
      | SOME enum_name =>
       (* Note serialization values may be compile-time known constants in general *)
       (case petr4_parse_serialization (tyenv, enummap, vtymap, gscope) enum_type members of
        | SOME_msg enummap_ser_updates =>
         (case ALOOKUP enummap enum_name of
          | SOME enum_mem_map =>
           SOME_msg (AUPDATE tyenv (enum_name, enum_type),
                     (AUPDATE enummap (enum_name,
                       AUPDATE_LIST enum_mem_map enummap_ser_updates)))
          | NONE =>
           SOME_msg (AUPDATE tyenv (enum_name, enum_type),
                     (AUPDATE enummap (enum_name, enummap_ser_updates))))
        | NONE_msg serialization_msg => NONE_msg serialization_msg)
      | NONE => get_error_msg "Could not parse name: " name)
    | NONE => get_error_msg "Could not parse type: " type)
  | _ => get_error_msg "Unknown JSON format of serializable enumeration type: " json
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

Definition petr4_postprocess_extern_method_call_def:
 petr4_postprocess_extern_method_call tyenv funn res_args tyargs =
  if incomplete_typeinf funn
  then
   (case get_typeinf_dummy_args tyenv tyargs of
    | SOME_msg targs =>
     SOME_msg (stmt_ass lval_null (e_call funn (res_args++targs)))
    | NONE_msg msg => NONE_msg msg)
  else
   SOME_msg (stmt_ass lval_null (e_call funn res_args))
End

Definition p4_seq_append_stmt_def:
 p4_seq_append_stmt stmt1 stmt2 =
  case (stmt1, stmt2) of
  | (stmt_empty, stmt_empty) => stmt_empty
  | (stmt_empty, stmt2) => stmt2
  | (stmt1, stmt_empty) => stmt1
  | _ => (stmt_seq stmt1 stmt2)
End

(**************************)
(* Inlining and prefixing *)

(* These are the two primitive prefixing schemes *)
Definition p4_prefix_vars_in_varn_def:
 p4_prefix_vars_in_varn gscope prefix varn =
  if MEM varn (MAP FST gscope)
  then varn
  else
   (case varn of
    | varn_name s =>
     (varn_name (prefix++("_"++s)))
    | _ => varn)
End
Definition p4_prefix_tbl_def:
 p4_prefix_tbl prefix tbl = (prefix++("."++tbl))
End

(* Here, prefixing of copyin-copyout parts happen *)
Definition petr4_inline_block_def:
 (petr4_inline_block gscope prefix body t_scope copyin copyout [] = SOME_msg (t_scope, p4_seq_append_stmt copyin (stmt_seq body copyout))) /\
 (petr4_inline_block gscope prefix body t_scope copyin copyout (((param_name, param_dir), arg, param_type)::t) = 
  (* This should just build on t_scope, copyin and copyout *)
  if is_d_out param_dir
  then
   (case get_lval_of_e arg of
    | SOME arg_lval =>
     let copyin' =
      if (param_dir <> d_out)
      then (p4_seq_append_stmt copyin (stmt_ass (lval_varname (p4_prefix_vars_in_varn gscope prefix (varn_name param_name))) arg))
      else (p4_seq_append_stmt copyin (stmt_ass (lval_varname (p4_prefix_vars_in_varn gscope prefix (varn_name param_name))) (e_v $ arb_from_tau param_type)))
     in
     let copyout' =
      if is_d_out param_dir
      then (p4_seq_append_stmt copyout (stmt_ass arg_lval (e_var (p4_prefix_vars_in_varn gscope prefix (varn_name param_name)))))
      else copyout
     in
     petr4_inline_block gscope prefix body (t_scope++[(varn_name param_name, (param_type, SOME arg_lval))]) copyin' copyout' t
    | NONE => NONE_msg ("Could not inline programmable block: argument passed into "++(param_name++" does not correspond to l-value.")))
  else
   let copyin' = (p4_seq_append_stmt copyin (stmt_ass (lval_varname (p4_prefix_vars_in_varn gscope prefix (varn_name param_name))) arg)) in
   petr4_inline_block gscope prefix body (t_scope++[(varn_name param_name, (param_type, NONE))]) copyin' copyout t
 )
End

(* Adds a prefix to the varname of every entry in a decl_list *)
Definition p4_prefix_decl_list_def:
 p4_prefix_decl_list gscope prefix (decl_list:t_scope) =
  MAP ( \ (h1, h2). (p4_prefix_vars_in_varn gscope prefix h1, h2)) decl_list
End

(* Sets the optional copyout L-value to NONE for all variables *)
Definition p4_remove_copyout_lval_decl_list_def:
 p4_remove_copyout_lval_decl_list (decl_list:t_scope) =
  MAP ( \ (h1, (h2, h3)). (h1, (h2, NONE:lval option))) decl_list
End

Definition p4_prefix_fname_def:
 p4_prefix_fname b_func_map prefix fname =
  if IS_SOME $ ALOOKUP b_func_map fname
  then (prefix++("."++fname))
  else fname
End

Definition p4_prefix_funn_def:
 p4_prefix_funn b_func_map prefix funn =
  case funn of
  | funn_name fname =>
   (funn_name (p4_prefix_fname b_func_map prefix fname))
  | _ => funn
End

Definition p4_prefix_vars_funs_in_e_def:
 p4_prefix_vars_funs_in_e gscope b_func_map prefix e =
  case e of
  | e_var varn => e_var (p4_prefix_vars_in_varn gscope prefix varn)
  | e_list el => e_list (MAP (p4_prefix_vars_funs_in_e gscope b_func_map prefix) el)
  | e_acc e' x => e_acc (p4_prefix_vars_funs_in_e gscope b_func_map prefix e') x
  | e_unop unop e' => e_unop unop (p4_prefix_vars_funs_in_e gscope b_func_map prefix e')
  | e_cast cast e' => e_cast cast (p4_prefix_vars_funs_in_e gscope b_func_map prefix e')
  | e_binop e' binop e'' =>
   e_binop (p4_prefix_vars_funs_in_e gscope b_func_map prefix e') binop (p4_prefix_vars_funs_in_e gscope b_func_map prefix e'')
  | e_concat e' e'' =>
   e_concat (p4_prefix_vars_funs_in_e gscope b_func_map prefix e') (p4_prefix_vars_funs_in_e gscope b_func_map prefix e'')
  | e_slice e' e'' e''' =>
   e_slice (p4_prefix_vars_funs_in_e gscope b_func_map prefix e') (p4_prefix_vars_funs_in_e gscope b_func_map prefix e'') (p4_prefix_vars_funs_in_e gscope b_func_map prefix e''')
  | e_call funn el =>
   e_call (p4_prefix_funn b_func_map prefix funn) (MAP (p4_prefix_vars_funs_in_e gscope b_func_map prefix) el)
  | e_select e' s_l_x_l x =>
   e_select (p4_prefix_vars_funs_in_e gscope b_func_map prefix e') s_l_x_l x
  | e_struct x_e_l =>
   e_struct (MAP ( \ (x,e). (x, p4_prefix_vars_funs_in_e gscope b_func_map prefix e)) x_e_l)
  | e_header b x_e_l =>
   e_header b (MAP ( \ (x,e). (x, p4_prefix_vars_funs_in_e gscope b_func_map prefix e)) x_e_l)
  | _ => e
Termination
WF_REL_TAC `measure (e_size o SND o SND o SND)` >>
fs[e_size_def] >>
rpt strip_tac >| [
 IMP_RES_TAC e1_tuple_size_mem >>
 fs[],

 IMP_RES_TAC e3_size_mem >>
 fs[],

 IMP_RES_TAC e3_size_mem >>
 fs[],

 IMP_RES_TAC e1_tuple_size_mem >>
 fs[]
]
End

Definition p4_prefix_vars_in_lval_def:
 p4_prefix_vars_in_lval gscope prefix lval =
  case lval of
  | lval_varname varn =>
   lval_varname (p4_prefix_vars_in_varn gscope prefix varn)
  | lval_field lval' x =>
   lval_field (p4_prefix_vars_in_lval gscope prefix lval') x
  | lval_slice lval' e e' =>
   (* Note that L-values cannot contain function calls *)
   lval_slice (p4_prefix_vars_in_lval gscope prefix lval') (p4_prefix_vars_funs_in_e gscope ([]:b_func_map) prefix e) (p4_prefix_vars_funs_in_e gscope ([]:b_func_map) prefix e')
  | lval_paren lval' => p4_prefix_vars_in_lval gscope prefix lval'
  | _ => lval
End

Definition p4_prefix_vars_tbls_funs_in_stmt_def:
 p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt  =
  case stmt of
  | stmt_ass lval e =>
   stmt_ass (p4_prefix_vars_in_lval gscope prefix lval) (p4_prefix_vars_funs_in_e gscope b_func_map prefix e)
  | stmt_cond e stmt1 stmt2 =>
   stmt_cond
    (p4_prefix_vars_funs_in_e gscope b_func_map prefix e)
    (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt1)
    (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt2)
  | stmt_block decl_list stmt' =>
   stmt_block (p4_prefix_decl_list gscope prefix decl_list) (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt')
  | stmt_ret e => stmt_ret (p4_prefix_vars_funs_in_e gscope b_func_map prefix e)
  | stmt_seq stmt1 stmt2 =>
   stmt_seq (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt1)
            (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix stmt2)
  | stmt_trans e => stmt_trans (p4_prefix_vars_funs_in_e gscope b_func_map prefix e)
  | stmt_app x el => stmt_app (p4_prefix_tbl prefix x) (MAP (p4_prefix_vars_funs_in_e gscope b_func_map prefix) el)
  | _ => stmt
End

Definition p4_prefix_vars_in_args_def:
 p4_prefix_vars_in_args prefix args =
  MAP ( \ (argname, dir). (prefix++("_"++argname), dir)) args
End

(* Note that this should not prefix global variables *)
(* TODO: Can an action call a global action with the same name? In that case, we
 * should make sure this does not prefix calls to functions of the same name *)
Definition p4_prefix_vars_in_b_func_map_def:
 p4_prefix_vars_in_b_func_map gscope prefix (b_func_map:b_func_map) =
  MAP ( \ (fname, (body, args)). (prefix++("."++fname), (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map prefix body, p4_prefix_vars_in_args prefix args))) b_func_map
End

Definition p4_prefix_tbls_in_tbl_map_def:
 p4_prefix_tbls_in_tbl_map b_func_map prefix (tbl_map:tbl_map_extra) =
  MAP ( \ (tbl_name, (mk_l, action_names, (def_action, e_l))). (prefix++("."++tbl_name), (mk_l, MAP (p4_prefix_fname b_func_map prefix) action_names, (p4_prefix_fname b_func_map prefix def_action, e_l)))) tbl_map
End

Definition p4_prefix_tbls_funs_in_tbl_entries_def:
 p4_prefix_tbls_funs_in_tbl_entries b_func_map prefix (tbl_entries:((string, (((e_list -> bool) # num), string # e_list) alist) alist)) =
  MAP (\ (name, upds).
       (prefix++("."++name),
        MAP (\ ((key, prio), (action_name, args)).
             ((key, prio), ((p4_prefix_fname b_func_map prefix action_name, args)))
            ) upds)
      ) tbl_entries
End

(* Prefixes tables only *)
Definition p4_prefix_tbls_in_stmt_def:
 p4_prefix_tbls_in_stmt prefix stmt =
  case stmt of
  | stmt_cond e stmt1 stmt2 =>
   stmt_cond
    e
    (p4_prefix_tbls_in_stmt prefix stmt1)
    (p4_prefix_tbls_in_stmt prefix stmt2)
  | stmt_block decl_list stmt' =>
   stmt_block decl_list (p4_prefix_tbls_in_stmt prefix stmt')
  | stmt_seq stmt1 stmt2 =>
   stmt_seq (p4_prefix_tbls_in_stmt prefix stmt1)
            (p4_prefix_tbls_in_stmt prefix stmt2)
  | stmt_app x el => stmt_app (p4_prefix_tbl prefix x) el
  | _ => stmt
End

Definition p4_stmt_contains_return_def:
 p4_stmt_contains_return stmt =
  case stmt of
  | stmt_cond e stmt1 stmt2 =>
   (p4_stmt_contains_return stmt1) \/
   (p4_stmt_contains_return stmt2)
  | stmt_block decl_list stmt =>
   (p4_stmt_contains_return stmt)
  | stmt_ret e => T
  | stmt_seq stmt1 stmt2 =>
   (p4_stmt_contains_return stmt1) \/
   (p4_stmt_contains_return stmt2)
  | _ => F
End


(**********************)
(* Common: statements *)

Definition petr4_parse_method_call_def:
 petr4_parse_method_call (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, func); (* Expression: either a name or a member (in case of extern object's method) *)
     (f2, Array tyargs); (* TODO: Type arguments. Typically an empty list: currently thrown away *)
     (f3, Array args)] => (* Argument list: typically expressions *)
   if f1 = "func" then
    (if f2 = "type_args" then
     (if f3 = "args" then
      (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (func, NONE) of
       | SOME_msg exp =>
        (case exp_to_funn (vtymap, extfun_list) exp of
         | SOME (SOME funn, obj_opt) =>
          let add_args =
           case funn of
            | funn_name fname =>
             (* For action, insert extra arguments with from_table F and hit bit as ARB *)
             if MEM fname action_list then [e_v $ v_bool F; e_v $ v_bool ARB] else []
            | _ => [] in
          let len_args = LENGTH args in
          (* Omit looking up types for methods with no args: quick fix for case of method with single optional arg.
           * Note return type is tossed away here anyhow *)
          (case (if len_args > 0 then find_fty_match_args ftymap funn len_args else SOME ([], p_tau_bot)) of
           | SOME (arg_tys, ret_ty) =>
            (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME arg_tys)) of
             | SOME_msg res_args =>
              (case funn of
               (* Extern object method, or method without associated object *)
               | (funn_ext ext_name extfun_name) =>
                if ext_name = ""
                then
                 (case petr4_postprocess_extern_method_call tyenv (funn_ext "" extfun_name) res_args tyargs of
                  | SOME_msg stmt => SOME_msg ([], [], [], [], [], stmt)
                  | NONE_msg postproc_ext_msg => NONE_msg postproc_ext_msg)
                else
                 (case obj_opt of
                  | SOME obj =>
                   (case petr4_postprocess_extern_method_call tyenv (funn_ext ext_name extfun_name) (obj::res_args) tyargs of
                    | SOME_msg stmt => SOME_msg ([], [], [], [], [], stmt)
                    | NONE_msg postproc_ext_msg => NONE_msg postproc_ext_msg)
                  | NONE => get_error_msg "no object provided for extern object method call: " func)
               | (funn_name fun_name) =>
                 SOME_msg ([], [], [], [], [], (stmt_ass lval_null (e_call funn (add_args++res_args))))
               | _ => get_error_msg "unknown type of method call: " func)
             | NONE_msg args_msg => NONE_msg ("could not parse method call: "++args_msg))
           | NONE => get_error_msg "type inference information not found for method call: " func)
         (* Apply or nested control block *)
         (* TODO: Can table names shadow control block (instance) names or vice versa? *)
         | SOME (NONE, SOME app_exp) =>
          (case app_exp of
           | (e_var (varn_name app_name)) =>
            (case ALOOKUP apply_map app_name of
             | SOME keys =>
              (case ALOOKUP tyenv app_name of
               | SOME block =>
                NONE_msg ("names of nested control block and table overlapping: "++app_name)
               | NONE =>
                SOME_msg ([], [], [], [], [], stmt_app app_name keys))
             | NONE =>
              (case ALOOKUP vtymap (varn_name app_name) of
               | SOME (p_tau_blk block_type_name) =>
                (case ALOOKUP pblock_map block_type_name of
                 | SOME ((pbl_type_control, params, b_func_map, decl_list, pars_map, tbl_map):pblock_extra, param_types) =>
                  (case FIND_EXTRACT_ONE (\ (k,v). k = block_type_name) b_func_map of
                   (* Params has format (string # dir) *)
                   | SOME ((name, (body, params')), b_func_map') =>
                    (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME (parameterise_taus param_types))) of
                     | SOME_msg res_args =>
                      if p4_stmt_contains_return body
                      then NONE_msg ("nested control block "++(app_name++(" of type "++(block_type_name++" contains a return statement, which is unsupported by the inlining scheme"))))
                      else
                       (* Prefixing of variables, tables and functions in body happens here *)
                       (case petr4_inline_block gscope app_name (p4_prefix_vars_tbls_funs_in_stmt gscope b_func_map app_name body) [] stmt_empty stmt_empty (ZIP(params, ZIP(res_args, param_types))) of
                        | SOME_msg (decl_list', stmt) =>
                         (case ALOOKUP tbl_entries_map block_type_name of
                          | SOME tbl_entries =>
                           (* TODO: Prefixing of variables in decl_list happens here - also prove it is OK *)
                           let inline_decl_list = p4_prefix_decl_list gscope app_name (decl_list'++decl_list) in
                           (* TODO: Prefixing of variables in local functions here, prove it is OK *)
                           SOME_msg (p4_prefix_vars_in_b_func_map gscope app_name b_func_map',
                                     p4_prefix_tbls_in_tbl_map b_func_map' app_name tbl_map,
                                     (* decl_list' is the parameters, decl_list is the pblock variables *)
                                     p4_remove_copyout_lval_decl_list inline_decl_list,
                                     p4_prefix_tbls_funs_in_tbl_entries b_func_map' app_name tbl_entries,
                                     (* List of taboo variable names *)
                                     MAP FST inline_decl_list,
                                     stmt)
                          | NONE => NONE_msg ("could not find control block in tbl_entries_map: "++block_type_name))
                        | NONE_msg inline_msg => NONE_msg inline_msg)
                     | NONE_msg args_msg => NONE_msg ("could not parse nested control block: "++args_msg))
                   | NONE => NONE_msg ("could not find instantiation of nested control block: "++block_type_name))
                 | _ => NONE_msg ("could not find control block: "++block_type_name))
               | _ =>
                NONE_msg ("could not find entry of control block name "++app_name++" in type environment"))
             | _ =>
              NONE_msg ("could not find entry of table name "++app_name++" in apply map"))
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
  | (e_slice exp' exp'' exp''') =>
   (case exp_to_lval exp' of
    | SOME lval => SOME (lval_slice lval exp'' exp''')
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Expand... *)
Definition infer_rhs_type_def:
 infer_rhs_type vtymap lval =
  case lval of
  | lval_varname varn =>
   ALOOKUP vtymap varn
  | lval_field lval' fld =>
   (case infer_rhs_type vtymap lval' of
    | SOME (p_tau_xtl struct_ty flds) =>
     ALOOKUP flds fld
    | _ => NONE)
  | lval_slice lval' exp exp' =>
   (case n_of_e_bitv exp of
    | SOME n =>
     (case n_of_e_bitv exp' of
      | SOME n' =>
       SOME (p_tau_bit ((n - n') + 1))
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE
End

Definition petr4_parse_assignment_def:
 petr4_parse_assignment (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, lhs); (* Left-hand side: expression, should be lval *)
     (f2, rhs)] => (* Right-hand side: expression *)
   if f1 = "lhs" then
    (if f2 = "rhs" then
     (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (lhs, NONE) of
      | SOME_msg lhs_res =>
       (case exp_to_lval lhs_res of
        | SOME lval => 
         (case infer_rhs_type vtymap lval of
          | SOME p_tau =>
           (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (rhs, SOME p_tau) of
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
 petr4_parse_return (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) stmt_details =
  case stmt_details of
  | [(f0, tags); (* No check for this, since it's only thrown away *)
     (f1, exp)] => (* Right-hand side: expression *)
   if f1 = "expr" then
     (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, NONE) of
      | SOME_msg exp_res => SOME_msg (stmt_ret exp_res)
      | NONE_msg exp_msg => NONE_msg ("could not parse return expression: "++exp_msg))
   else NONE_msg ("unknown JSON object field of return: "++f1)
  | _ => get_error_msg "unknown JSON format of return: " (Object stmt_details)
End

Definition petr4_parse_var_def:
 petr4_parse_var (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) var =
  case json_parse_obj ["tags"; "annotations"; "type"; "name"; "init"] var of
  | SOME [tags; annot; json_type; name; opt_init] =>
   (case petr4_parse_type tyenv json_type of
    | SOME tau_var =>
     (case petr4_parse_name name of
      | SOME var_name =>
       (case opt_init of
        | Null =>
         SOME_msg (varn_name var_name, tau_var, NONE)
        | val_exp =>
         (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (val_exp, SOME (parameterise_tau tau_var)) of
          | SOME_msg init =>
           SOME_msg (varn_name var_name, tau_var, SOME init)
          | NONE_msg init_val_msg => NONE_msg ("could not parse initial value: "++init_val_msg)))
      | NONE => get_error_msg "could not parse name: " name)
    | NONE => get_error_msg "could not parse type: " json_type)
  | _ => get_error_msg "unknown JSON format of variable: " var
End


(* TODO: use parse_arr and parse_obj *)
Definition petr4_parse_switch_cases_def:
 (petr4_parse_switch_cases p_tau [] =
  SOME_msg []) /\
 (petr4_parse_switch_cases p_tau (h::t) =
  (case json_parse_arr "Action" SOME h of
   | SOME act_obj =>
    (case json_parse_obj ["tags"; "label"; "code"] act_obj of
     | SOME [tags; label; code] =>
      (case petr4_parse_case_name label of
       | SOME label_res =>
        (case json_parse_obj ["tags"; "annotations"; "statements"] code of
         | SOME [tags'; annotations; Array stmts] =>
          (case petr4_parse_switch_cases p_tau t of
           | SOME_msg exps_res => SOME_msg ((label_res, stmts)::exps_res)
           | NONE_msg exps_msg => NONE_msg exps_msg)
         | _ => get_error_msg "unknown JSON format of switch case code: " code)
       | NONE => get_error_msg "could not parse switch case action name: " label)
     | _ => get_error_msg "unknown JSON format of switch case action: " act_obj)
   | _ => get_error_msg "unknown JSON format of switch case: " h)
 )
End

Triviality petr4_parse_switch_cases_size:
 !p_tau cases cases_res labels stmts.
 petr4_parse_switch_cases p_tau cases = SOME_msg cases_res ==>
 (labels,stmts) = UNZIP cases_res ==>
 SUM (MAP (\el. json3_size el + 1) stmts) < (json3_size cases + 1)
Proof
Induct_on ‘cases’ >- (
 rpt strip_tac >>
 fs[petr4_parse_switch_cases_def] >>
 rw[] >>
 fs[UNZIP]
) >>
rpt strip_tac >>
fs[petr4_parse_switch_cases_def] >>
Cases_on ‘json_parse_arr "Action" SOME h’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘json_parse_obj ["tags"; "label"; "code"] x’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘x'’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t'’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘petr4_parse_case_name h''’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘json_parse_obj ["tags"; "annotations"; "statements"] h'3'’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘x''’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t'’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘h'6'’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘t’ >> (fs[get_error_msg_distinct]) >>
Cases_on ‘petr4_parse_switch_cases p_tau cases ’ >> (fs[get_error_msg_distinct]) >>
rw[] >>
fs[UNZIP] >>
Cases_on ‘labels’ >> (fs[]) >>
Cases_on ‘stmts’ >> (fs[]) >>
subgoal ‘(t, t') = UNZIP a’ >- (
 fs[]
) >>
res_tac >>
rfs[] >>
subgoal ‘json3_size l + 1 < json3_size [h]’ >- (
 imp_res_tac json_parse_arr_size >>
 imp_res_tac json_parse_obj_size >>
 fs[json_size_def]
) >>
fs[json_size_def]
QED

(* TODO: Write better version *)
(* Currently only switches without fallthrough cases *)
Definition inline_switch_def:
 (inline_switch e [] = stmt_empty) /\
 (inline_switch e ((l,s)::t) =
  stmt_cond (e_binop e binop_eq l) s (inline_switch e t)
 )
End

Definition serialise_actions'_def:
 (serialise_actions' len action_list [] = SOME_msg []) /\
 (serialise_actions' len action_list (h::t) =
  case INDEX_FIND 0 (\el. el = h) action_list of
  | SOME (i, _) =>
   (case serialise_actions' len action_list t of
    | SOME_msg ser_res =>
     SOME_msg ((e_v $ v_bit (fixwidth 32 (n2v ((len-i)-1)), 32))::ser_res)
    | NONE_msg ser_msg => NONE_msg ser_msg)
  | NONE => NONE_msg (("could not serialise action: "++h)++"; not found in action list "++(merge_string_list action_list))
 )
End

(* TODO: In case of shadowing, last (visible) defined action with the name is used... *)
Definition serialise_actions_def:
 (serialise_actions action_list actions =
  serialise_actions' (LENGTH action_list) (REVERSE action_list) actions
 )
End

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
(* Note that the five first elements of the returned tuple
 * (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list)
 * are only used for inlining nested control blocks.
 * The next last element (vtymap_upds) is only used for passing along type inference information to
 * the transition at the end of parser states *)
Definition petr4_parse_stmts_def:
 (petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, (tbl_entries_map:(string # ((string, (((e_list -> bool) # num), string # e_list) alist) alist)) list), action_list, extfun_list) [] = SOME_msg ([], [], [], [], [], [], stmt_empty)) /\
  (petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) (h::t) =
  case h of
  | Array [String stmt_name; Object stmt_details] =>
   if stmt_name = "method_call" then
    (case petr4_parse_method_call (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) stmt_details of
     | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list', call_res) =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
       | SOME_msg (b_func_map_upds', tbl_map_upds', decl_list_upds', tbl_entries_upds', taboo_list, vtymap_upds, stmts_res) =>
        SOME_msg (b_func_map_upds++b_func_map_upds', tbl_map_upds++tbl_map_upds', decl_list_upds++decl_list_upds', tbl_entries_upds++tbl_entries_upds', taboo_list'++taboo_list, vtymap_upds, p4_seq_append_stmt call_res stmts_res)
       | NONE_msg stmts_msg => NONE_msg stmts_msg)
     | NONE_msg call_msg => NONE_msg call_msg)
   else if stmt_name = "assignment" then
    (case petr4_parse_assignment (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) stmt_details of
     | SOME_msg ass_res =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
       | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
        SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, p4_seq_append_stmt ass_res stmts_res)
       | NONE_msg stmts_msg => NONE_msg stmts_msg)
     | NONE_msg ass_msg => NONE_msg ass_msg)
   else if stmt_name = "conditional" then
    case stmt_details of
    | [(f0, tags); (* No check for this, since it's only thrown away *)
       (f1, cond); (* Condition: expression *)
       (f2, true_case); (* True case: statement *)
       (f3, false_case)] => (* False case: statement *)
     if f1 = "cond" then
      (if f2 = "tru" then
       (if f3 = "fls" then
        (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (cond, NONE) of
         | SOME_msg cond_res =>
          (* TODO: Will this work, since the cases are always a singleton list of a block statement? *)
          (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) [true_case] of
           | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, true_case_res) =>
            (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) [false_case] of
             | SOME_msg (b_func_map_upds', tbl_map_upds', decl_list_upds', tbl_entries_upds', taboo_list', vtymap_upds', false_case_res) =>
              (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
               | SOME_msg (b_func_map_upds'', tbl_map_upds'', decl_list_upds'', tbl_entries_upds'', taboo_list'', vtymap_upds'', stmts_res) =>
                SOME_msg (b_func_map_upds++b_func_map_upds'++b_func_map_upds'',
                          tbl_map_upds++tbl_map_upds'++tbl_map_upds'',
                          decl_list_upds++decl_list_upds'++decl_list_upds'',
                          tbl_entries_upds++tbl_entries_upds'++tbl_entries_upds'',
                          taboo_list++taboo_list'++taboo_list'',
                          vtymap_upds'',
                          p4_seq_append_stmt (stmt_cond cond_res true_case_res false_case_res) stmts_res)
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
        (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) stmts of
         | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) => 
          (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
           | SOME_msg (b_func_map_upds', tbl_map_upds', decl_list_upds', tbl_entries_upds', taboo_list', vtymap_upds', t_res) =>
            SOME_msg (b_func_map_upds++b_func_map_upds', tbl_map_upds++tbl_map_upds', decl_list_upds++decl_list_upds', tbl_entries_upds++tbl_entries_upds', taboo_list++taboo_list', vtymap_upds', p4_seq_append_stmt (stmt_block [] stmts_res) t_res)
           | NONE_msg t_msg => NONE_msg t_msg)
         | NONE_msg stmts_msg => NONE_msg ("could not parse block: "++stmts_msg)
        )
       | _ => get_error_msg "unknown JSON format of block: " block
      )
     else NONE_msg ("unknown JSON object field of block: "++f1)
    | _ => get_error_msg "unknown JSON format of block: " (Object stmt_details)
   else if stmt_name = "return" then
    (case petr4_parse_return (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) stmt_details of
     | SOME_msg ret_res =>
      (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
       | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
        SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, p4_seq_append_stmt ret_res stmts_res)
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
       (case petr4_parse_var (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) decl_obj of
        | SOME_msg (varn, tau, init_var_opt) =>
         (case petr4_parse_stmts (tyenv, enummap, (varn, parameterise_tau tau)::vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
          | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
           if MEM varn ((^apply_result_placeholder_varn)::taboo_list)
           then get_error_msg "taboo variable name found when parsing declaration statement: " decl_obj
           else
            (case init_var_opt of
             | SOME init_var =>
              SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, (varn, parameterise_tau tau)::vtymap_upds, stmt_block [(varn, tau, NONE)] (stmt_seq (stmt_ass (lval_varname varn) init_var) stmts_res))
             | NONE => SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, (varn, parameterise_tau tau)::vtymap_upds, stmt_block [(varn, tau, NONE)] stmts_res))
          | NONE_msg stmts_msg => NONE_msg stmts_msg)
        | NONE_msg varn_tau_msg => NONE_msg ("could not parse declaration: "++varn_tau_msg))
      | _ => get_error_msg "unknown JSON format of declaration: " decl)
    | _ => get_error_msg "unknown JSON format of declaration: " (Object stmt_details)
   else if stmt_name = "switch" then
    case stmt_details of
    | [("tags", tags);
       ("expr", expr);
       ("cases", Array cases)] =>
     (case petr4_parse_expression_gen (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (expr, NONE) of
      | SOME_msg (InlineApp [tbl_name] expr_res) =>
       let vtymap' = AUPDATE vtymap (varn_name tbl_name,
                                     p_tau_xtl struct_ty_struct [("hit", p_tau_bool);
                                                                 ("miss", p_tau_bool);
                                                                 ("action_run", p_tau_bit 32)]) in
       (case exp_to_p_tau (vtymap', ftymap) expr_res of
        | SOME p_tau =>
         (case petr4_parse_switch_cases p_tau cases of
          | SOME_msg cases_res =>
           let (labels, stmts) = UNZIP cases_res in
           (case serialise_actions action_list labels of
            | SOME_msg labels' =>
             (case petr4_parse_stmts_list (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) stmts of
              | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, stmts_res_list) =>
               (case ALOOKUP apply_map tbl_name of
                | SOME keys =>
                 (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
                  | SOME_msg (b_func_map_upds', tbl_map_upds', decl_list_upds', tbl_entries_upds', taboo_list', vtymap_upds, t_res) =>
                   let stmt =
                    stmt_block [(varn_name tbl_name,
                                (tau_xtl struct_ty_struct [("hit", tau_bool);
                                                           ("miss", tau_bool);
                                                           ("action_run", tau_bit 32)], NONE))]
                               (stmt_seq
                                (stmt_app tbl_name keys)
                                (stmt_seq
                                 (stmt_ass (lval_varname (varn_name tbl_name)) (e_var (^apply_result_placeholder_varn)))
                                 (inline_switch expr_res (ZIP(labels',stmts_res_list))))) in
                    SOME_msg (b_func_map_upds++b_func_map_upds', tbl_map_upds++tbl_map_upds', decl_list_upds++decl_list_upds', tbl_entries_upds++tbl_entries_upds', taboo_list++(taboo_list'++[varn_name tbl_name]), vtymap_upds, p4_seq_append_stmt stmt t_res)
                  | NONE_msg t_msg => NONE_msg t_msg)
                | NONE => NONE_msg ("table not found: "++tbl_name))
              | NONE_msg stmts_msg => NONE_msg stmts_msg)
            | NONE_msg act_msg => NONE_msg act_msg)
          | NONE_msg cases_msg => NONE_msg cases_msg)
        | NONE => get_error_msg "could not parse type of exp: " expr)
      | SOME_msg _ => get_error_msg "unsupported type of switch expression: " expr
      | NONE_msg expr_msg => NONE_msg ("could not parse switch expression: "++expr_msg))
    | _ => get_error_msg "unknown JSON format of switch: " (Object stmt_details)
   else if stmt_name = "empty_statement" then
    case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
    | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
     SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, p4_seq_append_stmt stmt_empty stmts_res)
    | NONE_msg stmts_msg => NONE_msg stmts_msg
   else NONE_msg ("unknown statement name: "++stmt_name)
  | Null =>
   (case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
    | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
     SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, p4_seq_append_stmt stmt_empty stmts_res)
    | NONE_msg stmts_msg => NONE_msg stmts_msg)
  | _ => get_error_msg "unknown JSON format of statement: " h) /\
 (* Same signature as above, but parses elementwise without merging into a single stmt *)
 (petr4_parse_stmts_list (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) [] =
  SOME_msg ([], [], [], [], [], [])) /\
 (petr4_parse_stmts_list (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) (h::t) =
  case petr4_parse_stmts (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) h of
  | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, vtymap_upds, stmts_res) =>
   (case petr4_parse_stmts_list (tyenv, enummap, vtymap, ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list, extfun_list) t of
    | SOME_msg (b_func_map_upds', tbl_map_upds', decl_list_upds', tbl_entries_upds', taboo_list', stmts_res_list) =>
     SOME_msg (b_func_map_upds++b_func_map_upds', tbl_map_upds++tbl_map_upds', decl_list_upds++decl_list_upds', tbl_entries_upds++tbl_entries_upds', taboo_list++taboo_list', (stmts_res::stmts_res_list))
    | NONE_msg msg' => NONE_msg msg')
  | NONE_msg msg => NONE_msg msg)
Termination
WF_REL_TAC `measure ( \ t. case t of | (INL (maps, json_list)) => json3_size json_list | (INR (maps, json_list_list)) => SUM (MAP (\ el . json3_size el + 1) json_list_list))` >>
rpt strip_tac >> (fs[json_size_def]) >- (
 fs[json_parse_obj_def, json_dest_obj_def, app_opt_def] >>
 Cases_on ‘p_2'’ >> (fs[]) >>
 rw[] >>
 Cases_on ‘l’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘h’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘t'’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘h’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘q' = "annotations"’ >> (fs[]) >>
 Cases_on ‘t''’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘h’ >> (fs[json_parse_obj'_def, app_opt_def]) >>
 Cases_on ‘q'' = "statements"’ >> (fs[]) >>
 Cases_on ‘json_parse_obj' [] t'’ >> (fs[json_size_def, app_opt_def])
) >- (
 (* Switch case *)
 IMP_RES_TAC petr4_parse_switch_cases_size >>
 res_tac >>
 fs[json_size_def, app_opt_def]
)
End


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
   | _ => get_error_msg "unknown JSON format of parameters: " h)
End

Definition update_vtymap_fun_def:
 (update_vtymap_fun vty_updates funtype =
  case funtype of
  | funtype_action => ([(varn_name "from_table", p_tau_bool); (varn_name "hit", p_tau_bool)]++vty_updates)
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
  | funtype_ext_function => (funn_ext "" f_name)
  | funtype_ext_obj_function obj_name => (funn_ext obj_name f_name)
  | funtype_ext_obj_constructor obj_name => (funn_inst obj_name))
End

Definition petr4_parse_ret_ty_opt_def:
 petr4_parse_ret_ty_opt tyenv funtype fa_name ret_ty_opt =
  case ret_ty_opt of
   | NONE =>
    (* Only actions and constructors have NONE return type *)
    if funtype = funtype_action
    then SOME_msg p_tau_bot
    else SOME_msg $ p_tau_ext fa_name
   | SOME ret_ty =>
    (case petr4_parse_ptype T tyenv ret_ty of
     | SOME ret_p_tau => SOME_msg ret_p_tau
     | NONE => get_error_msg "could not parse return type: " ret_ty)
End

(* Parses the shared parts of actions and functions *)
(* TODO: Rename this *)
Definition petr4_parse_fun_body_def:
 petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (body, ret_ty_opt, name, params, funtype) =
  case json_parse_obj ["tags"; "annotations"; "statements"] body of
   | SOME [body_tags; body_annot; stmts_arr] =>
    (case json_dest_arr stmts_arr of
     | SOME stmts =>
      (case petr4_parse_name name of
       | SOME fa_name =>
        (case petr4_parse_ret_ty_opt tyenv funtype fa_name ret_ty_opt of
         | SOME_msg ret_p_tau =>
          (case petr4_parse_p_params F tyenv params of
           | SOME_msg (fa_params, p_vty_updates) =>
            (* Note that no programmable blocks can be nested inside functions *)
            (* Note that no tables can be applied inside functions *)
            (case petr4_parse_stmts (tyenv, enummap, (update_vtymap_fun p_vty_updates funtype)++vtymap, ftymap, gscope, [], apply_map, [], action_list, extfun_list) stmts of
             | SOME_msg (_, _, _, _, _, _, fa_body) =>
              let add_params =
               if funtype = funtype_action
               then [("from_table", d_in); ("hit", d_in)]
               else [] in
              SOME_msg ((fa_name, (fa_body, add_params++fa_params)),
                        (get_funn_name funtype fa_name, (MAP SND p_vty_updates, ret_p_tau)))
             | NONE_msg stmts_msg => NONE_msg stmts_msg)
           | NONE_msg params_msg => NONE_msg ("could not parse parameters: "++params_msg))
         | NONE_msg ret_msg => NONE_msg ret_msg)
       | NONE => get_error_msg "could not parse name: " name)
     | _ => get_error_msg "function or action body not JSON Array: " stmts_arr)
   | _ => get_error_msg "unknown JSON format of function or action body: " body
End

(* Used by functions for parsing top-level functions and similar, also used directly
 * for parsing block-local actions and extern object methods *)
Definition petr4_fun_to_fmapupdate_def:
 petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) fun funtype =
  case funtype of
  | funtype_action =>
   (case json_parse_obj ["tags"; "annotations"; "name"; "params"; "body"] fun of
    | SOME [tags; annot; name; Array params; body] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (body, NONE, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of action: " fun)
  | funtype_function =>
   (case json_parse_obj ["tags"; "return"; "name"; "type_params"; "params"; "body"] fun of
    | SOME [tags; ret_ty; name; Array typarams; Array params; body] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (body, SOME ret_ty, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of function: " fun)
  | funtype_ext_function =>
   (case json_parse_obj ["tags"; "annotations"; "return"; "name"; "type_params"; "params"] fun of
    | SOME [tags; annot; ret_ty; name; Array typarams; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], SOME ret_ty, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern function: " fun)
  | funtype_ext_obj_function obj_name =>
   (case json_parse_obj ["tags"; "annotations"; "return"; "name"; "type_params"; "params"] fun of
    | SOME [tags; annot; ret_ty; name; Array typarams; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], SOME ret_ty, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern function: " fun)
  | funtype_ext_obj_constructor obj_name =>
   (case json_parse_obj ["tags"; "annotations"; "name"; "params"] fun of
    | SOME [tags; annot; name; Array params] =>
     petr4_parse_fun_body (tyenv, enummap, vtymap, ftymap, fmap, gscope, apply_map, action_list, extfun_list) (Object [("tags", Null); ("annotations", Null); ("statements", Array [])], NONE, name, params, funtype)
    | _ => get_error_msg "unknown JSON format of extern constructor: " fun)
End

Definition is_final_stmt_return_def:
 is_final_stmt_return stmt =
  case stmt of
 | stmt_empty => F
 | stmt_ass lval e => F
 | stmt_cond e stmt1 stmt2 =>
  is_final_stmt_return stmt1 /\ is_final_stmt_return stmt2
 | stmt_block decl_list stmt => is_final_stmt_return stmt
 | stmt_ret e => T
 | stmt_seq stmt1 stmt2 =>
  is_final_stmt_return stmt2  
 | stmt_trans e => F
 | stmt_app x el => F
 | stmt_ext => F
End

Definition add_explicit_return_def:
 add_explicit_return stmt =
  if is_final_stmt_return stmt
  then stmt
  else (stmt_seq stmt (stmt_ret (e_v v_bot)))
End

(* This adds an assignment to gen_apply_result as the first statement of every action *)
Definition add_apply_result_inline_def:
 add_apply_result_inline action_list stmt action_name =
  (case serialise_actions action_list [action_name] of
   | SOME_msg [ser_res] =>
    let struct = (e_struct [("hit", e_var (varn_name "hit"));
                            ("miss", e_unop unop_neg (e_var (varn_name "hit")));
                            ("action_run", ser_res)]) in
    SOME_msg (stmt_seq (stmt_cond (e_var (varn_name "from_table")) (stmt_ass (lval_varname (^apply_result_placeholder_varn)) struct) stmt_empty) stmt)
   | NONE_msg ser_msg => NONE_msg ser_msg
   | _ => NONE_msg ("different than expected number of action serialisations was returned for: "++(action_name++" using action list "++(merge_string_list action_list))))
End

(* The below to replace arguments to actions in nested actions to pay forward
 * "from_table" and "hit" *)
Definition replace_action_args_e_def:
 replace_action_args_e e action_list =
  case e of
  | e_call (funn_name f_name) e_l =>
   if MEM f_name action_list
   then e_call (funn_name f_name) ([e_var (varn_name "from_table"); e_var (varn_name "hit")]++(DROP 2 e_l))
   else e
  | _ => e
End
Definition replace_action_args_def:
 replace_action_args stmt action_list =
  case stmt of
  | stmt_cond e stmt' stmt'' =>
   stmt_cond e (replace_action_args stmt' action_list) (replace_action_args stmt'' action_list)
  | stmt_block t_scope stmt' =>
   stmt_block t_scope (replace_action_args stmt' action_list)
  | stmt_seq stmt' stmt'' =>
   stmt_seq (replace_action_args stmt' action_list) (replace_action_args stmt'' action_list)
  | stmt_ass lval e => stmt_ass lval (replace_action_args_e e action_list)
  | _ => stmt
End

(* TODO: Decide whether to put action in global or local function map here, re-use in parse_locals *)
(* Parses a top-level action (note that this can't see any tables, since those can only be defined in control blocks) *)
Definition petr4_parse_actiondef_def:
 petr4_parse_actiondef (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) action =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, [], action_list, extfun_list) action funtype_action of
   | SOME_msg ((fa_name, (fa_body, fa_params)), ftymap_upd) =>
    if ALL_DISTINCT ((^apply_result_placeholder)::(MAP FST fa_params))
    then
     (case add_apply_result_inline (action_list++[fa_name]) (add_explicit_return fa_body) fa_name of
      | SOME_msg fa_body' =>
       SOME_msg (ftymap_upd, [fa_name], (fa_name, (replace_action_args fa_body' action_list, fa_params)))
      | NONE_msg inl_msg => NONE_msg inl_msg)
    else NONE_msg ("Inlining scheme for apply expressions caused overlapping parameter names (hit or gen_apply_result) while parsing action "++fa_name)
   | NONE_msg msg => NONE_msg ("Could not parse action: "++msg)
End

(* TODO: Decide whether to put action in global or local function map here, re-use in parse_locals *)
(* Parses a top-level function *)
Definition petr4_parse_function_def:
 petr4_parse_function (tyenv, enummap, vtymap, ftymap, fmap, gscope, extfun_list) function =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, fmap, gscope, [], [], extfun_list) function funtype_function of
   | SOME_msg (fmap_upd, ftymap_upd) =>
    SOME_msg (ftymap_upd::ftymap, AUPDATE fmap fmap_upd)
   | NONE_msg msg => NONE_msg ("Could not parse function: "++msg)
End

(* Parses a top-level extern function, saves the name in extfun_list, action_list *)
Definition petr4_parse_extfun_def:
 petr4_parse_extfun (tyenv, enummap, vtymap, ftymap, extfun_list) extfun =
  case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, []:func_map, []:scope, [], [], extfun_list) extfun funtype_ext_function of
   | SOME_msg ((extfun_name, _), ftymap_upd) =>
    SOME_msg (AUPDATE ftymap ftymap_upd, extfun_list++[extfun_name])
   | NONE_msg m_msg => NONE_msg ("could not parse extern function: "++m_msg)
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
 (petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap, extfun_list) ext_name [] =
  SOME_msg ftymap) /\
 (petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap, extfun_list) ext_name (h::t) =
  case h of
   | Array [String "Method"; met_obj] =>
    (case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, []:func_map, []:scope, [], [], extfun_list) met_obj (funtype_ext_obj_function ext_name) of
     | SOME_msg (_, ftymap_upd) =>
      petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap_upd::ftymap, extfun_list) ext_name t
     | NONE_msg m_msg => NONE_msg ("could not parse extern method: "++m_msg))
   | Array [String "Constructor"; con_obj] =>
    (case petr4_fun_to_fmapupdate (tyenv, enummap, vtymap, ftymap, []:func_map, []:scope, [], [], extfun_list) con_obj (funtype_ext_obj_constructor ext_name) of
     | SOME_msg (_, ftymap_upd) =>
      petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap_upd::ftymap, extfun_list) ext_name t
     | NONE_msg c_msg => NONE_msg ("could not parse extern constructor: "++c_msg))
   | _ => get_error_msg "unknown JSON format of extern method: " h)
End

(* TODO: Add support for type parameters *)
Definition petr4_parse_ext_object_def:
 petr4_parse_ext_object (tyenv, enummap, vtymap, ftymap, extfun_list) ext_obj =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "methods"] ext_obj of
   | SOME [tags; annot; name_obj; Array typarams; Array methods] =>
    (case petr4_parse_name name_obj of
     | SOME ext_name => 
      (case petr4_parse_ext_methods (tyenv, enummap, vtymap, ftymap, extfun_list) ext_name methods of
       | SOME_msg ftymap' => 
        SOME_msg (AUPDATE tyenv (ext_name, p_tau_ext ext_name), ftymap')
       | NONE_msg met_msg => NONE_msg ("Could not parse extern object methods: "++met_msg))
     | NONE => get_error_msg "Could not parse name: " name_obj)
   | _ => get_error_msg "Could not parse extern object: " ext_obj
End

(**********)
(* Parser *)

(* This parses a type specialisation (as encountered during instantiation) to
 * a name and a list of pseudo-type arguments targ1, targ2, ... *)
Definition petr4_parse_targs_def:
 petr4_parse_targs tyenv json_type =
  case json_type of
  | Array [String type_str; type_obj] =>
   if type_str = "name"
   then
    (* Nested block *)
    (case json_parse_obj ["tags"; "name"] type_obj of
     | SOME [tags; name] =>
      (case petr4_parse_bare_name name of
       | SOME bl_name =>
        SOME_msg (bl_name, [])
       | NONE => get_error_msg "could not parse programmable block name: " name)
     | _ => get_error_msg "unknown JSON format of programmable block type specialisation: " type_obj)
   else if type_str = "specialized"
   then
    (* Extern object *)
    (case json_parse_obj ["tags"; "base"; "args"] type_obj of
     | SOME [tags; base_type; Array targs] =>
      (case petr4_parse_type tyenv base_type of
       | SOME tau_ext =>
        (case petr4_parse_type_name base_type of
         | SOME type_name =>
          (case get_typeinf_dummy_args tyenv targs of
           | SOME_msg targs_res => SOME_msg (type_name, targs_res)
           | NONE_msg targs_msg => NONE_msg ("could not parse type specialisation: "++targs_msg))
         | _ => get_error_msg "could not parse type name: " json_type)
       | SOME _ => get_error_msg "base type is not extern: " base_type
       | NONE => get_error_msg "could not parse base type: " base_type)
     | _ => get_error_msg "unknown JSON format of extern object type specialisation: " type_obj)
   else get_error_msg "unknown JSON format of type specialisation: " json_type
  | _ => get_error_msg "unknown JSON format of type specialisation: " json_type
End

(* TODO: Infer types of arguments *)
Definition petr4_parse_inst_def:
 petr4_parse_inst (tyenv, enummap, vtymap, ftymap, decl_list, gscope, inits, extfun_list) inst =
  (* TODO: Use init field *)
  case json_parse_obj ["tags"; "annotations"; "type"; "args"; "name"; "init"] inst of
  | SOME [tags; annot; json_type; Array args; name; init] =>
   (case petr4_parse_targs tyenv json_type of
    | SOME_msg (type_name, targs) =>
     (case ALOOKUP tyenv type_name of
      | SOME (p_tau_blk _) =>
       (case petr4_parse_name name of
        | SOME blk_name =>
         SOME_msg (decl_list,
                   inits,
                   (varn_name blk_name, p_tau_blk type_name))
        | NONE => get_error_msg "could not parse name: " name)
      | SOME (p_tau_ext _) =>
       (case find_fty_match_args ftymap (funn_inst type_name) (LENGTH args) of
        | SOME (arg_tys, ret_ty) =>
         (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME arg_tys)) of
          | SOME_msg res_args => 
           (case petr4_parse_name name of
            | SOME inst_name =>
             SOME_msg (decl_list++[(varn_name inst_name, tau_ext, NONE)],
                       p4_seq_append_stmt inits (stmt_ass lval_null (e_call (funn_inst type_name) ([e_var (varn_name inst_name)]++(res_args++targs)))),
                       (varn_name inst_name, p_tau_ext type_name))
            | NONE => get_error_msg "could not parse name: " name)
          | NONE_msg args_msg => NONE_msg ("could not parse instantiation arguments: "++args_msg))
        | NONE => get_error_msg "could not find type information of instantiation: " json_type)
      | _ => get_error_msg "could not instantiate type: " json_type)
    | NONE_msg targs_msg => NONE_msg ("could not parse instantiation type: "++targs_msg))
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
   else if mk_str = "range"
   then SOME_msg mk_range
   else if mk_str = "optional"
   then SOME_msg mk_optional
   else if mk_str = "selector"
   then SOME_msg mk_selector
   else NONE_msg ("unknown match kind: "++mk_str)
  | _ => get_error_msg "unknown JSON format of match kind: " match_kind
End

Definition petr4_parse_keys_def:
 (petr4_parse_keys (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) [] = SOME_msg []) /\
 (petr4_parse_keys (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (h::t) =
   case json_parse_obj ["tags"; "annotations"; "key"; "match_kind"] h of
   | SOME [tags; annot; key; match_kind] =>
    (case petr4_parse_match_kind match_kind of
     | SOME_msg res_mk =>
      (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (key, NONE) of
       | SOME_msg res_key =>
        (case exp_to_p_tau (vtymap, ftymap) res_key of
         | SOME p_tau =>
          (case deparameterise_tau p_tau of
           | SOME res_tau =>
            (case petr4_parse_keys (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
             | SOME_msg res_msg => SOME_msg ((res_key, res_mk, res_tau)::res_msg)
             | NONE_msg err_msg => NONE_msg err_msg)
           | NONE => get_error_msg "key has parameter type: " h)
         | NONE => get_error_msg "could not infer type of key: " h)
       | NONE_msg key_msg => NONE_msg ("could not parse key: "++key_msg))
     | NONE_msg mk_msg => NONE_msg ("could not parse match kind: "++mk_msg))
   | _ => get_error_msg "unknown JSON format of key: " h)
End

(* Used to add arguments to actions inside table *)
Definition add_desugar_args_def:
 add_desugar_args hit args = [(e_v $ v_bool T); (e_v $ v_bool hit)]++args
End

Definition petr4_parse_action_def:
 petr4_parse_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) action =
  case json_parse_obj ["tags"; "annotations"; "name"; "args"] action of
   | SOME [tags; annot; name; Array args] =>
(* TODO: This section is probably needed when actions with arguments are encountered
    (* TODO: This sequence of functions that parses arguments with type inference is duplicated
     * several times in this file. Make it a separate function instead. *)
    (* Actions may only be actions and not e.g. extern method calls, but we might want to do 
     * type inference of arguments *)
    (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (name, NONE) of
     | SOME_msg exp =>
      (case exp_to_funn vtymap exp of
       | SOME (SOME (funn_name action_name), obj_opt) =>
        (case find_fty_match_args ftymap (funn_name action_name) (LENGTH args) of
         | SOME (arg_tys, ret_ty) =>
          (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME arg_tys)) of
           | SOME_msg res_args =>
            (case petr4_parse_actions (tyenv, enummap, vtymap, ftymap) t of
             | SOME_msg res_msg => SOME_msg ((action_name, res_args)::res_msg)
             | NONE_msg err_msg => NONE_msg err_msg)
           | NONE_msg args_msg => NONE_msg ("could not parse action arguments: "++args_msg))
         | NONE => get_error_msg "type inference information not found for action: " name)
       | _ => get_error_msg "could not parse action name into funn: " name)
     | NONE_msg act_name_msg => NONE_msg ("could not parse action: "++act_name_msg))
*)
    (case petr4_parse_bare_name name of
     | SOME action_name =>
      (case find_fty_match_args ftymap (funn_name action_name) (LENGTH args) of
       | SOME (arg_tys, ret_ty) =>
        (case petr4_parse_args (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (args, MAP SOME arg_tys)) of
         | SOME_msg args_res => SOME_msg (action_name, add_desugar_args T args_res)
         | NONE_msg args_msg => NONE_msg args_msg)
       | NONE => get_error_msg "type inference information not found for action: " name)
     | NONE => get_error_msg "could not parse action name (expected BareName): " name)
   | _ => get_error_msg "unknown JSON format of action: " action
End

Definition petr4_parse_action_names_def:
 (petr4_parse_action_names (tyenv, enummap, vtymap, ftymap) [] = SOME_msg []) /\
 (petr4_parse_action_names (tyenv, enummap, vtymap, ftymap) (h::t) =
  (case json_parse_obj ["tags"; "annotations"; "name"; "args"] h of
   | SOME [tags; annot; name; Array args] =>
    (case petr4_parse_bare_name name of
     | SOME action_name =>
      (case petr4_parse_action_names (tyenv, enummap, vtymap, ftymap) t of
       | SOME_msg res_msg => SOME_msg (action_name::res_msg)
       | NONE_msg err_msg' => NONE_msg err_msg')
     | NONE => get_error_msg "could not parse action name (expected BareName): " name)
   | _ => get_error_msg "unknown JSON format of action name: " h))
End

(* TODO: Action argument seems to not be exported by petr4 *)
Definition petr4_parse_default_action_def:
 petr4_parse_default_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) default_action =
  (* TODO: Don't throw const away *)
  case json_parse_obj ["tags"; "annotations"; "const"; "name"; "value"] default_action of
  | SOME [tags; annot; const; name; action] =>
   (case petr4_parse_name name of
    | SOME custom_name =>
     if custom_name = "default_action" then
     (case petr4_parse_expression (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (action, NONE) of
      | SOME_msg (e_call (funn_name action_name) args) =>
       SOME_msg (action_name, args)
      | SOME_msg (e_var (varn_name action_name)) =>
       SOME_msg (action_name, [])
      | NONE_msg exp_msg => NONE_msg ("could not parse default action: "++exp_msg)
      | _ => get_error_msg "unknown format of default action name: " action)
     else get_error_msg ("unknown table property field ("++(custom_name++"): ")) default_action
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown format of table property field: " default_action
End

Definition p4_get_v_bitv_def:
 p4_get_v_bitv v =
  case v of
  | v_bit (bl, n) => SOME (bl,n)
  | _ => NONE
End

(* TODO: Move? *)
Definition p4_get_v_bit_width_def:
 p4_get_v_bit_width v =
  case p4_get_v_bitv v of
  | SOME (bl, n) => SOME n
  | _ => NONE
End

(* TODO: Move? *)
Definition count_prefix_def:
 (count_prefix [] (acc:num) = acc) /\
 (count_prefix (T::t) acc = count_prefix t (acc+1)) /\
 (count_prefix (F::t) acc = acc)
End

(* TODO: Move? *)
Definition p4_get_prefix_length_def:
 p4_get_prefix_length v =
  case p4_get_v_bitv v of
  | SOME (bl, n) => SOME (count_prefix bl 0)
  | _ => NONE
End

(* TODO: Merge with petr4_parse_matches *)
(* This always gives everything priority 0 unless match kind is LPM, in which
 * case the priority becomes the length of the prefix *)
Definition petr4_parse_entry_def:
 (petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) [] = SOME_msg []) /\
 (petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) ((key, (key_type, mk))::t) =
  case key of
  | Array [String key_str; key_obj] =>
   if key_str = "Expression"
   then
    (case json_parse_obj ["tags"; "expr"] key_obj of
     | SOME [tags; exp] =>
      (case exp of
       | Array [String exp_str; exp_obj] =>
        (* Mask expressions constitute a special case *)
        if exp_str = "mask"
        then
         (case json_parse_obj ["tags"; "expr"; "mask"] exp_obj of
          | SOME [mask_tags; mask_exp; mask] =>
           (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (mask_exp, SOME key_type) of
            | SOME_msg val_res =>
             (case p4_get_v_bitv val_res of
              | SOME val_bitv =>
               (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (mask, SOME key_type) of
                 | SOME_msg mask_res =>
                  (case p4_get_v_bitv mask_res of
                   | SOME mask_bitv =>
                    if mk = mk_lpm
                    then
                     (case p4_get_prefix_length mask_res of
                      | SOME n =>
                       (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
                        | SOME_msg entry_res => SOME_msg ((s_mask val_bitv mask_bitv, n)::entry_res)
                        | NONE_msg entry_msg => NONE_msg entry_msg)
                      | NONE => get_error_msg "could not get prefix length of table entry: " exp_obj)
                    else
                     (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
                      | SOME_msg entry_res => SOME_msg ((s_mask val_bitv mask_bitv, 0)::entry_res)
                      | NONE_msg entry_msg => NONE_msg entry_msg)
                   | _ => get_error_msg "bitmask mask is not a bitv: " mask)
                 | NONE_msg mask_exp_msg => NONE_msg ("could not parse bit mask table entry expression: "++mask_exp_msg))
               | _ => get_error_msg "bitmask value is not a bitv: " mask_exp)
            | NONE_msg exp_msg => NONE_msg ("could not parse bit mask table entry expression: "++exp_msg))
          | _ => get_error_msg "unknown JSON format of bit mask table entry: " exp_obj)
        (* Range expressions constitute another special case *)
        else if exp_str = "range"
        then
         (case json_parse_obj ["tags"; "lo"; "hi"] exp_obj of
          | SOME [range_tags; range_lo; range_hi] =>
           (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (range_lo, SOME key_type) of
            | SOME_msg lo_res =>
             (case p4_get_v_bitv lo_res of
              | SOME lo_bitv =>
               (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (range_hi, SOME key_type) of
                | SOME_msg hi_res =>
                 (case p4_get_v_bitv hi_res of
                  | SOME hi_bitv =>
                   (* Cannot be LPM *)
                   (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
                    | SOME_msg entry_res => SOME_msg ((s_range lo_bitv hi_bitv, 0)::entry_res)
                    | NONE_msg entry_msg => NONE_msg entry_msg)
                  | _ => get_error_msg "range upper bound is not a bitv: " range_hi)
                | NONE_msg hi_msg => NONE_msg ("could not parse range table entry expression: "++hi_msg))
              | _ => get_error_msg "range lower bound is not a bitv: " range_lo)
            | NONE_msg lo_msg => NONE_msg ("could not parse range table entry expression: "++lo_msg))
          | _ => get_error_msg "unknown JSON format of range table entry: " exp_obj)
        else
         (* TODO: Matches should be restricted to constants known at compile time *)
         (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, SOME key_type) of
           | SOME_msg val_res =>
            if mk = mk_lpm
            then
             (case p4_get_v_bit_width val_res of
              | SOME n =>
               (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
                | SOME_msg entry_res => SOME_msg ((s_sing val_res, n)::entry_res)
                | NONE_msg entry_msg => NONE_msg entry_msg)
              | NONE => get_error_msg "could not get width of constant table entry: " exp)
            else
             (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
              | SOME_msg entry_res => SOME_msg ((s_sing val_res, 0)::entry_res)
              | NONE_msg entry_msg => NONE_msg entry_msg)
           | NONE_msg exp_msg => NONE_msg ("could not parse constant table entry: "++exp_msg))
       | _ => get_error_msg "unknown JSON format of table entry key expression: " exp)
     | _ => get_error_msg "unknown JSON format of table entry key: " key_obj)
   else if key_str = "DontCare"
   then
    (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
     | SOME_msg entry_res => SOME_msg ((s_univ, 0)::entry_res)
     | NONE_msg entry_msg => NONE_msg entry_msg)
   else get_error_msg "unknown JSON format of table entry: " key
  | _ => get_error_msg "unknown JSON format of table entry: " key)
End

Definition get_max_prio_def:
 (get_max_prio [] acc = acc) /\
 (get_max_prio (h::t) acc = get_max_prio t (MAX h acc))
End

Definition petr4_annot_is_priority_def:
 petr4_annot_is_priority annot =
  case json_parse_obj ["tags"; "name"; "body"] annot of
  | SOME [tags; name; body] =>
   (case json_parse_obj ["tags"; "string"] name of
    | SOME [tags'; String string] =>
     if string = "priority"
     then T
     else F
    | _ => F)
  | _ => F
End

(* TODO: Currently, rest of annotations are discarded *)
Definition petr4_parse_priority_def:
 petr4_parse_priority annot =
  case FIND_EXTRACT_ONE petr4_annot_is_priority annot of
  | SOME (prio, annot') =>
   (case json_parse_obj ["tags"; "name"; "body"] prio of
    | SOME [tags; name; body] =>
     (case body of
      | Array [String unparsed_str; prio_obj] =>
       if unparsed_str = "Unparsed"
       then
        (case json_parse_obj ["tags"; "str"] prio_obj of
         | SOME [tags; Array str_list] =>
          (case str_list of
           | [str_obj] =>
            (case json_parse_obj ["tags"; "string"] str_obj of
             | SOME [tags''; String string] => SOME $ s2n 10 UNHEX string
             | _ => NONE)
           | _ => NONE)
         | _ => NONE)
        else NONE
      | _ => NONE)
    | _ => NONE)
  | NONE => NONE
End

Definition petr4_parse_entries_def:
 (petr4_parse_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) key_type_mk_list [] = SOME_msg []) /\
 (petr4_parse_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) key_type_mk_list (h::t) =
   case json_parse_obj ["tags"; "annotations"; "matches"; "action"] h of
   (* TODO: Get priority from annotation *)
   | SOME [tags; Array annot; Array matches; action] =>
    (case petr4_parse_entry (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP (matches, key_type_mk_list)) of
     | SOME_msg matches_res =>
      (case petr4_parse_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) action of
       | SOME_msg (action_name, args) =>
        (case petr4_parse_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) key_type_mk_list t of
         | SOME_msg res_msg =>
          let prio' = (case petr4_parse_priority annot of | SOME annot_prio => annot_prio | NONE => (get_max_prio (MAP SND matches_res) 0)) in
           SOME_msg (((( \ k. match_all_e k (MAP FST matches_res)), prio'), (action_name, args))::res_msg)
         | NONE_msg err_msg => NONE_msg err_msg)
       | NONE_msg exp_msg => NONE_msg ("could not parse table entry action: "++exp_msg))
     | NONE_msg matches_msg => NONE_msg ("could not parse table entry key matches: "++matches_msg))
   | _ => get_error_msg "unknown JSON format of table entry: " h)
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
  | (Array [String "Entries"; obj]) => T
  | _ => F
End

Definition petr4_process_key_def:
 petr4_process_key (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props =
  (* TODO: Replace with FIND_EXTRACT_ONE_OR_NONE *)
  case FIND_EXTRACT_ONE petr4_property_is_key props of
  | SOME (keys, props') =>
   (case keys of
    | Array [String "Key"; Object [("tags", tags); ("keys", Array keys_obj)]] =>
     (case petr4_parse_keys (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) keys_obj of
      | SOME_msg key_mk_tau_list => SOME_msg (key_mk_tau_list, props')
      | NONE_msg msg => NONE_msg msg)
    | _ => get_error_msg "unknown key property format: " keys)
  | NONE => SOME_msg ([], props)
End

(* TODO: Add more here later when needed *)
Definition petr4_process_actions_def:
 petr4_process_actions (tyenv, enummap, vtymap, ftymap) props =
  case FIND_EXTRACT_ONE petr4_property_is_actions props of
  | SOME (actions, props') =>
   (case actions of
    | Array [String "Actions"; actions_obj] =>
     (case json_parse_obj ["tags"; "actions"] actions_obj of
      | SOME [tags; Array actions_list] =>
       (case petr4_parse_action_names (tyenv, enummap, vtymap, ftymap) actions_list of
        | SOME_msg actions_res => SOME_msg (actions_res, props')
        | NONE_msg msg => NONE_msg msg)
      | _ => get_error_msg "could not parse actions: " actions_obj)
    | _ => get_error_msg "unknown actions property format: " actions)
  | NONE => get_error_msg "zero or duplicate actions property fields in table: " (Array props)
End

Definition petr4_process_default_action_def:
 petr4_process_default_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props =
  case FIND_EXTRACT_ONE petr4_property_is_default_action props of
  | SOME (default_action, props') =>
   (case default_action of
    | Array [String "Custom"; custom_obj] =>
     (case petr4_parse_default_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) custom_obj of
      | SOME_msg (action_name, args) => SOME_msg ((action_name, add_desugar_args F args), props')
      | NONE_msg msg => NONE_msg msg)
    | _ => get_error_msg "unknown default action property format: " default_action)
  | NONE => SOME_msg (("NoAction", add_desugar_args F []), props)
End

(* TODO: Add stuff here as needed *)
Definition petr4_process_size_def:
 petr4_process_size props = SOME_msg props
End

Definition petr4_process_entries_def:
 petr4_process_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) key_mk_list props =
  case FIND_EXTRACT_ONE petr4_property_is_entries props of
  | SOME (entries, props') =>
   (case entries of
    | Array [String "Entries"; entries_obj] =>
     (case json_parse_obj ["tags"; "entries"] entries_obj of
      | SOME [tags; Array entries_list] =>
       (case petr4_parse_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) key_mk_list entries_list of
        | SOME_msg entries_res => SOME_msg (entries_res, props')
        | NONE_msg msg => NONE_msg msg)
      | _ => get_error_msg "could not parse table entries: " entries_obj)
    | _ => get_error_msg "unknown table entries property format: " entries)
  | NONE => SOME_msg ([], props)
End

(* TODO: This should take arch_pkg_opt and be able to discard properties based on which
 * architecture you're parsing. Currently, it just discards everything, potentially allowing
 * for false positives (programs that appear correctly parsed) in case of arch-specific properties
 * which would matter for execution *)
Definition petr4_process_arch_specific_properties_def:
 petr4_process_arch_specific_properties props = SOME_msg props
End

Definition petr4_process_properties_def:
 petr4_process_properties (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props =
  case petr4_process_key (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props of
  | SOME_msg (key_mk_tau_list, props') =>
   (case petr4_process_actions (tyenv, enummap, vtymap, ftymap) props' of
    | SOME_msg (action_names, props'') =>
     (case petr4_process_default_action (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props'' of
      | SOME_msg (default_action, props''') =>
       (case petr4_process_size props''' of
        | SOME_msg props'''' =>
         (case exps_to_p_taus (vtymap, ftymap) (MAP FST key_mk_tau_list) of
          | SOME key_list =>
           (case petr4_process_entries (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP(key_list, MAP (FST o SND) key_mk_tau_list)) props'''' of
            | SOME_msg (entries, props''''') =>
             (* TODO: implementation field is eBPF-specific? *)
             (case petr4_process_arch_specific_properties props''''' of
              | SOME_msg arch_props_res =>
               (case key_mk_tau_list of
                | [] =>
                 SOME_msg ([], action_names, default_action, entries)
                | _ => SOME_msg (key_mk_tau_list, action_names, default_action, entries))
              | NONE_msg arch_props_msg => NONE_msg arch_props_msg)
            | NONE_msg entries_props_msg => NONE_msg entries_props_msg)
          | NONE => NONE_msg "could not get types of key expressions")
        | NONE_msg size_msg => NONE_msg size_msg)
      | NONE_msg default_action_msg => NONE_msg default_action_msg)
    | NONE_msg actions_msg => NONE_msg actions_msg)
  | NONE_msg key_msg => NONE_msg key_msg
End

Definition str_contains_def:
 str_contains s c = MEM c $ EXPLODE s
End

Definition petr4_parse_table_def:
 petr4_parse_table (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) table =
  case json_parse_obj ["tags"; "annotations"; "name"; "properties"] table of
  | SOME [tags; annot; name; Array props] =>
   (* Properties are: Key, Actions
    * Optional properties: size, default_action, entries, largest_priority_wins, priority_delta *)
   (case petr4_parse_name name of
    | SOME tbl_name =>
     (* TODO: Is this unnecessary, since names with periods are not allowed anyway? *)
     if str_contains tbl_name #"."
     then get_error_msg "(local) table name contains a period, which is unsupported by the inlining scheme: " name
     else
      (case petr4_process_properties (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) props of
       | SOME_msg (keys, action_names, default_action, entries) =>
        SOME_msg ((tbl_name, (MAP (FST o SND) keys, action_names, default_action)), (tbl_name, MAP FST keys), (tbl_name, entries), (tbl_name, MAP (SND o SND) keys))
       | NONE_msg prop_msg => NONE_msg ("could not parse properties: "++prop_msg))
    | NONE => get_error_msg "could not parse name: " name)
  | _ => get_error_msg "unknown JSON format of table: " table
End

(* TODO: Use json_parse_arr_list *)
Definition petr4_parse_locals_def:
 (petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map:b_func_map, local_ftymap, tbl_map:tbl_map_extra, decl_list, inits, apply_map, tbl_entries, ttymap) [] =
  SOME_msg (vtymap, b_func_map, local_ftymap, tbl_map, decl_list, inits, apply_map, tbl_entries, ttymap, action_list)) /\
 (petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map, local_ftymap, tbl_map, decl_list, inits, apply_map, tbl_entries, ttymap) (h::t) =
  case h of
   | Array [String local_string; local_obj] =>
    if local_string = "Instantiation"
    then
     (case petr4_parse_inst (tyenv, enummap, vtymap, ftymap, decl_list, gscope, inits, extfun_list) local_obj of
      | SOME_msg (decl_list', inits', vty_upd) =>
       petr4_parse_locals (tyenv, enummap, vty_upd::vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map, local_ftymap, tbl_map, decl_list', inits', apply_map, tbl_entries, ttymap) t
      | NONE_msg inst_msg => NONE_msg ("could not parse instantiation: "++inst_msg))
    else if local_string = "Action"
    then
     (case petr4_parse_actiondef (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) local_obj of
      | SOME_msg (local_ftymap_upd, action_list_upds, fmap_upd) =>
       petr4_parse_locals (tyenv, enummap, vtymap, AUPDATE ftymap local_ftymap_upd, fmap, gscope, action_list++action_list_upds, extfun_list) (AUPDATE b_func_map fmap_upd, AUPDATE local_ftymap local_ftymap_upd, tbl_map, decl_list, inits, apply_map, tbl_entries, ttymap) t
      | NONE_msg actiondef_msg => NONE_msg ("could not parse block-local action: "++actiondef_msg)
     )
    else if local_string = "Variable"
    then
     (case petr4_parse_var (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) local_obj of
      | SOME_msg (varn, tau, init_opt) =>
       (case init_opt of
        | SOME init_var =>
         petr4_parse_locals (tyenv, enummap, (varn, parameterise_tau tau)::vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map, local_ftymap, tbl_map, decl_list++[(varn, tau, NONE)], stmt_seq inits (stmt_ass (lval_varname varn) init_var), apply_map, tbl_entries, ttymap) t
        | NONE =>
         petr4_parse_locals (tyenv, enummap, (varn, parameterise_tau tau)::vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map, local_ftymap, tbl_map, decl_list++[(varn, tau, NONE)], inits, apply_map, tbl_entries, ttymap) t)
      | NONE_msg var_msg => NONE_msg ("could not parse block-local variable: "++var_msg))
    else if local_string = "Constant"
    then
     (case petr4_parse_constant (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) local_obj of
      | SOME_msg (vtymap', gscope') =>
       petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope', action_list, extfun_list) (b_func_map, local_ftymap, tbl_map, decl_list, inits, apply_map, tbl_entries, ttymap) t
      | NONE_msg const_msg => NONE_msg ("could not parse block-local constant: "++const_msg))
    else if local_string = "Table"
    then
     (case petr4_parse_table (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) local_obj of
      | SOME_msg (tbl_map_entry, apply_map_entry, tbl_entry_updates, ttymap_update) =>
       petr4_parse_locals (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) (b_func_map, local_ftymap, AUPDATE tbl_map tbl_map_entry, decl_list, inits, AUPDATE apply_map apply_map_entry, tbl_entries++[tbl_entry_updates], AUPDATE ttymap ttymap_update) t
      | NONE_msg tbl_msg => NONE_msg ("could not parse table: "++tbl_msg))
    else get_error_msg "unknown JSON format of local: " h
   | _ => get_error_msg "unknown JSON format of local: " h)
End

(* TODO: Use OPTION_BIND, parse_arr and parse_obj *)
Definition petr4_parse_matches_def:
 (petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) [] = SOME_msg []) /\
 (petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) ((h,expected_tau)::t) =
  case h of
  | Array [String "Expression";
           Object [("tags", tags); ("expr", exp)]] =>
   (* TODO: Note that this is technically more restrictive than the P4 definition, where select cases are expressions,
    *       not necessarily values. Most targets probably restrict to values in practice though. *)
   (case petr4_parse_value (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (exp, SOME expected_tau) of
     | SOME_msg val_res =>
      (case petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
       | SOME_msg matches_res => SOME_msg ((s_sing val_res)::matches_res)
       | NONE_msg matches_msg => NONE_msg matches_msg)
     | NONE_msg exp_msg => NONE_msg ("could not parse select match case: "++exp_msg))
  | Array [String "Default";
           Object [("tags", tags)]] =>
   (case petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
    | SOME_msg matches_res => SOME_msg (s_univ::matches_res)
    | NONE_msg matches_msg => NONE_msg matches_msg)
  | Array [String "DontCare";
           Object [("tags", tags)]] =>
   (case petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) t of
    | SOME_msg matches_res => SOME_msg (s_univ::matches_res)
    | NONE_msg matches_msg => NONE_msg matches_msg)
  | _ => get_error_msg "unknown JSON format of select case match: " h)
End

Definition petr4_parse_case_def:
 petr4_parse_case (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) expected_taus select_case =
  case json_parse_obj ["tags"; "matches"; "next"] select_case of
   | SOME [tags; Array match_exps; name] =>
    (case petr4_parse_name name of
     | SOME state_name =>
      let n_matches = LENGTH expected_taus in
      if (LENGTH match_exps = n_matches)
      then
       (case petr4_parse_matches (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP(match_exps,expected_taus)) of
        | SOME_msg matches_res => SOME_msg (matches_res, state_name)
        | NONE_msg exp_msg => NONE_msg ("could not parse expression: "++exp_msg))
      else
       (* Only the default case has fewer elements than expected *)
       SOME_msg (REPLICATE n_matches s_univ, state_name)
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "unknown JSON format of case: " select_case
End

Definition is_default_case_def:
 (is_default_case [] = T) /\
 (is_default_case (h::t) =
  if h = s_univ
  then (is_default_case t)
  else F)
End

(* TODO: Rewrite from tail-recursive to avoid code duplication? *)
Definition petr4_parse_cases_def:
 (petr4_parse_cases (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) expected_taus [] =
  SOME_msg []) /\
 (petr4_parse_cases (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) expected_taus (h::t) =
  case petr4_parse_case (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) expected_taus h of
   | SOME_msg exp_case_res =>
    if is_default_case (FST exp_case_res)
    then SOME_msg [exp_case_res]
    else
     (case petr4_parse_cases (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) expected_taus t of
      | SOME_msg exp_cases_res => SOME_msg (exp_case_res::exp_cases_res)
      | NONE_msg cases_msg => NONE_msg cases_msg)
   | NONE_msg case_msg => NONE_msg ("could not parse cases: "++case_msg))
End

(* TODO: Use json_parse_arr_list *)
Definition petr4_parse_trans_def:
 petr4_parse_trans (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) trans =
  case trans of
  | [String "Direct";
     Object [("tags", tags);
             ("next", next)]] =>
   (case petr4_parse_name next of
    | SOME next_state =>
     SOME_msg (stmt_trans (e_v (v_str next_state)), F)
    | NONE => get_error_msg "could not parse name: " next)
  | [String "Select";
     Object [("tags", tags);
             ("exprs", Array exps);
             ("cases", Array cases)]] =>
    (case petr4_parse_expressions (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) (ZIP(exps, REPLICATE (LENGTH exps) NONE)) of
     | SOME_msg exps_res =>
      (case exps_to_p_taus (vtymap, ftymap) exps_res of
       | SOME p_taus =>
        (case petr4_parse_cases (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) p_taus cases of
         | SOME_msg cases_res =>
          if is_default_case (FST $ LAST cases_res)
          then SOME_msg (stmt_trans (e_select (e_struct (ZIP(REPLICATE (LENGTH exps_res) "",exps_res))) (BUTLASTN 1 cases_res) (SND $ LAST cases_res)), F)
          else SOME_msg (stmt_trans (e_select (e_struct (ZIP(REPLICATE (LENGTH exps_res) "",exps_res))) cases_res "set_no_match"), T)
         | NONE_msg cases_msg => get_error_msg (cases_msg++" while parsing transition: ") (Array trans))
       | NONE => get_error_msg "could not parse type of transition expressions: " (Array exps))
     | NONE_msg exps_msg => get_error_msg (exps_msg++" while parsing transition: ") (Array trans)
     | _ => get_error_msg ("lists of expressions in select statements not supported, encountered while parsing transition: ") (Array trans))
  | _ => get_error_msg "unknown JSON format of transition: " (Array trans)
End

Definition add_set_no_match_state_def:
 add_set_no_match_state pars_map =
  if EXISTS (\ (n, stmt). n = "set_no_match") pars_map
  then NONE_msg "encountered reserved parser state name set_no_match in P4 program"
  else
   SOME_msg (AUPDATE pars_map ("set_no_match",
                              stmt_ass lval_null (e_call (funn_ext "" "verify")
                               [e_v (v_bool F);
                                e_v (v_bit (fixwidth 32 (n2v 2), 32))])))
End

(* TODO: This ignores nested programmable blocks, for now *)
Definition petr4_parse_states_def:
 (petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope,extfun_list) (pars_map:pars_map) [] =
  SOME_msg pars_map) /\
 (petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope,extfun_list) pars_map (h::t) =
  case json_parse_obj ["tags"; "annotations"; "name"; "statements"; "transition"] h of
   | SOME [tags; annot; name; Array stmts; Array trans] =>
    (case petr4_parse_name name of
     | SOME state_name =>
      (case petr4_parse_stmts (tyenv,enummap,vtymap,ftymap,gscope,[],[],[],[],extfun_list) stmts of
       | SOME_msg (_, _, _, _, _, vtymap_upds, stmts_res) =>
        (case petr4_parse_trans (tyenv,enummap,vtymap_upds++vtymap,ftymap,gscope,extfun_list) trans of
         | SOME_msg (trans_res, F) =>
          petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope,extfun_list) (AUPDATE pars_map (state_name, stmt_seq stmts_res trans_res)) t
         | SOME_msg (trans_res, T) =>
          (case petr4_parse_states (tyenv,enummap,vtymap,ftymap,gscope,extfun_list) (AUPDATE pars_map (state_name, stmt_seq stmts_res trans_res)) t of
           | SOME_msg pars_map =>
            add_set_no_match_state pars_map
           | NONE_msg stats_msg => NONE_msg stats_msg)
         | NONE_msg trans_msg => NONE_msg ("could not parse parser state: "++trans_msg))
       | NONE_msg stmts_msg => NONE_msg ("could not parse parser state body: "++stmts_msg))
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "unknown JSON format of parser state: " h)
End

(* TODO: Remove "THE" hack? Shouldn't make difference... *)
Definition petr4_parse_parser_def:
 petr4_parse_parser (tyenv, enummap:enummap, vtymap, ftymap, blftymap, fmap:func_map, bltymap, gscope, pblock_map, extfun_list) parser =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params";
                       "constructor_params"; "locals"; "states"] parser of
   | SOME [tags; annot; name; Array typarams; Array params; Array constructor_params; Array locals; Array states] =>
    (case petr4_parse_name name of
     | SOME parser_name =>
      (* TODO: Modify vtymap directly here instead? *)
      (case petr4_parse_p_params F tyenv params of
       | SOME_msg (pars_params, vty_updates) =>
        (case petr4_parse_locals (tyenv, enummap, vty_updates++vtymap, ftymap, fmap, gscope, [], extfun_list) ([], [], [], [], stmt_empty, [], [], []) locals of
         | SOME_msg (vtymap', b_func_map, local_ftymap, tbl_map, decl_list, inits, apply_map, tbl_entries, ttymap, action_list') =>
          (case petr4_parse_states (tyenv, enummap, vtymap', AUPDATE_LIST ftymap local_ftymap, gscope, extfun_list) [] states of
           | SOME_msg pars_map =>
            SOME_msg (tyenv, enummap, ftymap, AUPDATE blftymap (parser_name, local_ftymap), fmap, bltymap, gscope, AUPDATE pblock_map (parser_name, ((pbl_type_parser, pars_params, (b_func_map++[(parser_name, (stmt_seq inits (stmt_trans (e_v (v_str "start"))), []))]), decl_list, pars_map, tbl_map), MAP (THE o deparameterise_tau o SND) vty_updates)))
           | NONE_msg states_msg => NONE_msg ("Could not parse states: "++states_msg++" while parsing parser "++parser_name))
         | NONE_msg locals_msg => NONE_msg ("Could not parse locals: "++locals_msg++" while parsing parser "++parser_name))
       | NONE_msg blparams_msg => NONE_msg ("Could not parse block parameters: "++blparams_msg++" while parsing parser "++parser_name))
     | NONE => get_error_msg "could not parse name: " name)
   | _ => get_error_msg "Unknown JSON format of parser: " parser
End

(* Like AUPDATE, but returns NONE when an entry already exists *)
(* TODO: Move? *)
Definition AUPDATE_FRESH_def:
 AUPDATE_FRESH alist (k,v) =
  case ALOOKUP alist k of
   | SOME _ => NONE
   | NONE => SOME (alist++[(k,v)])
End

Definition AUPDATE_FRESH_LIST_def:
 AUPDATE_FRESH_LIST alist k_v_list =
  FOLDL ( \ l_opt (k,v). case l_opt of | SOME l => AUPDATE_FRESH l (k,v) | NONE => NONE) (SOME alist) k_v_list
End


(***********)
(* Control *)

(* This function checks for redundant (permissible) duplicates in updates,
 * and then merges them. These can occur e.g. when the same nested block is
 * applied twice. *)
(* TODO: Return an NONE_msg with the exact error *)
Definition petr4_merge_upds_def:
 petr4_merge_upds upds =
  FOLDL (\ wip_upds_opt (k, v). case wip_upds_opt of
                         | SOME wip_upds =>
                          if ~(MEM (k,v) wip_upds)
                          then
                           let upds_dup = FILTER (\ (k',v'). k'=k) upds in
                           if EVERY (\ (k',v'). v'=v) upds_dup
                           then SOME ((k, v)::wip_upds)
                           else NONE (* This means an illegal duplicate has been found *)
                          else SOME wip_upds
                         | NONE => NONE
        ) (SOME []) upds
End

Definition check_taboos_def:
 check_taboos gscope decl_list ctrl_params taboo_list control_name f =
  let decl_list' = (MAP FST decl_list) in
  let ctrl_params' = (MAP (varn_name o FST) ctrl_params) in
  let gscope' = (MAP FST gscope) in
  if (EVERY (\ el. ~(MEM el decl_list')) taboo_list)
  then
   (if (EVERY (\ el. ~(MEM el ctrl_params')) taboo_list)
    then
     (if (EVERY (\ el. ~(MEM el gscope')) taboo_list)
      then f
      else NONE_msg (("Taboo variable from block: "++control_name)++" found among global variables"))
    else NONE_msg ("Taboo variable found among block parameters in block: "++control_name))
  else NONE_msg ("Taboo variable found among block variables in block: "++control_name)
End

(* TODO: Remove "THE" hack? Shouldn't make difference... *)
Definition petr4_parse_control_def:
 petr4_parse_control (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, gscope, pblock_map, tbl_entries_map, action_list, extfun_list, ttymap) control =
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
          (case petr4_parse_locals (tyenv, enummap, vty_updates++vtymap, ftymap, fmap, gscope, action_list, extfun_list) ([], [], [], [], stmt_empty, [], [], []) locals of
           | SOME_msg (vtymap', b_func_map, local_ftymap, tbl_map, decl_list, inits, apply_map, tbl_entries', ttymap', action_list') =>
            (case petr4_parse_stmts (tyenv, enummap, vtymap', AUPDATE_LIST ftymap local_ftymap, gscope, pblock_map, apply_map, tbl_entries_map, action_list', extfun_list) stmts of
             | SOME_msg (b_func_map_upds, tbl_map_upds, decl_list_upds, tbl_entries_upds, taboo_list, _, res_apply) =>
              (* All elements of decl_list_upds are taboo, but not all taboo variables are in decl_list_upds *)
              check_taboos gscope decl_list ctrl_params taboo_list control_name 
(
              let b_func_map' = (b_func_map++[(control_name, (stmt_seq inits res_apply, []))]) in
              (* TODO: Try new names instead of returning errors *)
              (* This will safely merge inlined variables, functions and tables
               * (if any conflicting maps are encountered, the import tool will stop with an error) *)
              (case petr4_merge_upds (b_func_map'++b_func_map_upds) of
               | SOME b_func_map'' =>
                (case petr4_merge_upds (tbl_map++tbl_map_upds) of
                 | SOME tbl_map' =>
                  (case petr4_merge_upds (decl_list++decl_list_upds) of
                   | SOME decl_list' =>
                   SOME_msg (AUPDATE tyenv (control_name, p_tau_blk control_name), enummap, ftymap, AUPDATE blftymap (control_name, local_ftymap), fmap, bltymap, gscope, AUPDATE pblock_map (control_name, ((pbl_type_control, ctrl_params, b_func_map'', decl_list', ([]:pars_map), tbl_map')), MAP (THE o deparameterise_tau o SND) vty_updates), (tbl_entries_map++[(control_name, AUPDATE_LIST tbl_entries' tbl_entries_upds)]), action_list', AUPDATE_LIST ttymap ttymap')
                   | NONE => NONE_msg ("Duplicate variable (parameter) name in nested control block while parsing control "++control_name))
                 | NONE => NONE_msg ("Duplicate table name in nested control block while parsing control "++control_name))
               | NONE => NONE_msg ("Local function in nested control block has same name as (and is different from) local function in parent block; encountered while parsing control "++control_name))
)
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
Definition petr4_p_tau_pars_to_string_def:
 (petr4_p_tau_pars_to_string [] = SOME []) /\
 (petr4_p_tau_pars_to_string (h::t) =
   case petr4_p_tau_par_to_string h of
   | SOME res =>
    (case petr4_p_tau_pars_to_string t of
     | SOME res_tl => SOME (res::res_tl)
     | NONE => NONE)
   | NONE => NONE)
End

Definition petr4_parse_package_type_def:
 petr4_parse_package_type (tyenv, ptymap) package_type =
  case json_parse_obj ["tags"; "annotations"; "name"; "type_params"; "params"] package_type of
  | SOME [tags; annot; name; type_params; Array params] =>
   (case petr4_parse_p_params T tyenv params of
     (* res_dirs contains tuples of parameter names and directions *)
     (* e_params contains tuples of parameter varn_names and p_types *)
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

Definition get_arch_block_pbl_name_def:
 get_arch_block_pbl_name arch_block =
  case arch_block of
   | (arch_block_pbl pbl_name params) => SOME pbl_name
   | _ => NONE
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

(* TODO: This should also parse top-level instantiation of externs *)
Definition petr4_parse_top_level_inst_def:
 petr4_parse_top_level_inst (tyenv, bltymap, ptymap) inst =
  case json_parse_obj ["tags"; "annotations"; "type"; "args"; "name"; "init"] inst of
  | SOME [tags; annot; type; Array args; name; init] =>
   (case petr4_parse_type_name type of
    | SOME inst_type_name =>
     (* Check type of inst in tyenv (extern object or package) *)
     (case ALOOKUP tyenv inst_type_name of
      | SOME (p_tau_pkg pkg_name) =>
       (case ALOOKUP ptymap inst_type_name of
        | SOME pkg_param_tys =>
         (case petr4_parse_pblock_insts args of
          | SOME args_res =>
           (case petr4_get_arch_block_pbls bltymap (ZIP (args_res, pkg_param_tys)) of
            | SOME ab_pbls => SOME_msg (ab_pbls, pkg_name)
            | NONE => get_error_msg "Could not parse programmable block instantiations: " (Array args))
          | NONE => get_error_msg "Could not parse top-level instantiation arguments: " (Array args))
        | NONE => get_error_msg "Unknown package type: " type)
      | SOME (p_tau_ext ext_name) =>
       (get_error_msg "Top-level extern instantiations currently unsupported by HOL4P4: " inst)
      | _ => get_error_msg "Unknown type of top-level instantiation: " inst)
    | NONE => get_error_msg "Could not parse type name (may be top-level extern instantiation): " type)
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

Definition p4_get_pbl_def:
 p4_get_pbl ab_list pbl_name =
  FIND (\ab. case ab of
             | arch_block_pbl pbl_name' params => pbl_name' = pbl_name
             | _ => F) ab_list
End

Definition p4_extract_action_names_map_def:
 p4_extract_action_names_map ((pblock_name, ((pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map):pblock_extra, args))) =
  let
   (tbl_map', action_names_map) = UNZIP $ MAP (\ (tbl_name, (mk_l, action_names, default_action)). ((tbl_name, (mk_l, default_action)), (tbl_name, action_names))) tbl_map
  in
   ((pblock_name, ((pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map'), args)), (pblock_name, action_names_map))
End

Definition p4_clean_pblock_map_def:
 p4_clean_pblock_map pblock_map ab_list =
  let pblock_map' = FILTER (\ (pbl_name, pbl). IS_SOME $ p4_get_pbl ab_list pbl_name) pblock_map in
  let (pblock_map'', pblock_action_names_map) = UNZIP $ MAP p4_extract_action_names_map pblock_map' in
   (pblock_map'', pblock_action_names_map)
End

(* This transforms the tbl_entries_map into a list of (global, with prefixes) tbl_updates *)
Definition p4_clean_tbl_entries_map_def:
 p4_clean_tbl_entries_map tbl_entries_map ab_list =
  FLAT $
   (MAP SND) $
    FILTER (\ (pbl_name, tbl_entries). IS_SOME $ p4_get_pbl ab_list pbl_name) tbl_entries_map
End

(* TODO: Make wrapper function for errors, so error messages can include the local variable context *)
(* NOTE: action_list is a list of all functions which are actions. *)
Definition petr4_parse_element_def:
 petr4_parse_element (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map:(string # (pblock_extra # tau list)) list, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) json =
  case json of
  | Array [String elem_name; obj] =>
   if elem_name = "Error" then
    (case petr4_parse_error enummap obj of
     | SOME_msg enummap' =>
      SOME_dbg (tyenv, enummap', vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "MatchKind" then
    (case petr4_parse_match_kind_typedef enummap obj of
     | SOME_msg enummap' =>
      SOME_dbg (tyenv, enummap', vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Enum" then
    (case petr4_parse_enum enummap obj of
     | SOME_msg enummap' =>
      SOME_dbg (tyenv, enummap', vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "SerializableEnum" then
    (case petr4_parse_serializable_enum (tyenv, enummap, vtymap, gscope) obj of
     | SOME_msg (tyenv', enummap') =>
      SOME_dbg (tyenv', enummap', vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   (* WIP: Extern object types added to the type environment, since parameters to blocks
    * can be of extern type. *)
   else if elem_name = "ExternObject" then
    (case petr4_parse_ext_object (tyenv, enummap, vtymap, ftymap, extfun_list) obj of
     | SOME_msg (tyenv', ftymap') =>
      SOME_dbg (tyenv', enummap, vtymap, ftymap', blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "ExternFunction" then
    (case petr4_parse_extfun (tyenv, enummap, vtymap, ftymap, extfun_list) obj of
     | SOME_msg (ftymap', extfun_list') =>
      SOME_dbg (tyenv, enummap, vtymap, ftymap', blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list', ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Action" then
    (case petr4_parse_actiondef (tyenv, enummap, vtymap, ftymap, fmap, gscope, action_list, extfun_list) obj of
     | SOME_msg (ftymap_upd, action_list_upds, fmap_upd) =>
      SOME_dbg (tyenv, enummap, vtymap, AUPDATE ftymap ftymap_upd, blftymap, AUPDATE fmap fmap_upd, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list++action_list_upds, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Function" then
    (case petr4_parse_function (tyenv, enummap, vtymap, ftymap, fmap, gscope, extfun_list) obj of
     | SOME_msg (ftymap', fmap') =>
      SOME_dbg (tyenv, enummap, vtymap, ftymap', blftymap, fmap', bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "TypeDef" then
    (case petr4_parse_typedef tyenv obj of
     | SOME_msg tyenv' =>
      SOME_dbg (tyenv', enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   (* TODO: Constants are added to the global scope, also vtymap if not arbitrary-length constant... *)
   else if elem_name = "Constant" then
    (case petr4_parse_constant (tyenv, enummap, vtymap, ftymap, gscope, extfun_list) obj of
     | SOME_msg (vtymap', gscope') =>
      SOME_dbg (tyenv, enummap, vtymap', ftymap, blftymap, fmap, bltymap, ptymap, gscope', pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Struct" then
    (case petr4_parse_struct tyenv obj struct_ty_struct of
     | SOME_msg tyenv' =>
      SOME_dbg (tyenv', enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Header" then
    (case petr4_parse_struct tyenv obj struct_ty_header of
     | SOME_msg tyenv' =>
      SOME_dbg (tyenv', enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   (* TODO: Fix default parameter values *)
   else if elem_name = "ParserType" then
    (case petr4_parse_block_type (tyenv, fmap, bltymap, gscope) pbl_type_parser obj of
     | SOME_msg bltymap' =>
      SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap', ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   (* TODO: Fix default parameter values *)
   else if elem_name = "ControlType" then
    (case petr4_parse_block_type (tyenv, fmap, bltymap, gscope) pbl_type_control obj of
     | SOME_msg bltymap' =>
      SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap', ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   (* TODO: Fix parser and control I/O *)
   else if elem_name = "Parser" then
    (case petr4_parse_parser (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, gscope, pblock_map, extfun_list) obj of
     | SOME_msg (tyenv', enummap', ftymap', blftymap', fmap', bltymap', gscope', pblock_map') =>
      SOME_dbg (tyenv', enummap', vtymap, ftymap', blftymap', fmap', bltymap', ptymap, gscope', pblock_map', tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "control" then
    (case petr4_parse_control (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, gscope, pblock_map, tbl_entries_map, action_list, extfun_list, ttymap) obj of
     | SOME_msg (tyenv', enummap', ftymap', blftymap', fmap', bltymap', gscope', pblock_map', tbl_entries_map', action_list', ttymap') =>
      SOME_dbg (tyenv', enummap', vtymap, ftymap', blftymap', fmap', bltymap', ptymap, gscope', pblock_map', tbl_entries_map', arch_pkg_opt, ab_list, action_list, extfun_list, ttymap')
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "PackageType" then
    (case petr4_parse_package_type (tyenv, ptymap) obj of
     | SOME_msg (tyenv', ptymap') =>
      SOME_dbg (tyenv', enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap', gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap)
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else if elem_name = "Instantiation" then
    (case petr4_parse_top_level_inst (tyenv, bltymap, ptymap) obj of
     | SOME_msg (ab_list', pkg_name) =>
      (case arch_pkg_opt of
       (* VSS: Only one top-level package exists *)
       | SOME (arch_vss (NONE)) =>
        (case get_arch_block_pbl_name (EL 0 ab_list') of
         | SOME pbl_name =>
          (case ALOOKUP pblock_map pbl_name of
           | SOME (pblock, argtys) =>
            SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, SOME (arch_vss (SOME (vss_pkg_VSS (EL 1 argtys)))), vss_add_ff_blocks ab_list', action_list, extfun_list, ttymap)
           | _ => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Unknown programmable block in top-level package instantiation: "++pbl_name))
         | NONE => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Invalid block in top-level package instantiation"))
       | SOME (arch_vss _) =>
        NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Duplicate top-level package instantiations")
       (* eBPF: Only one top-level package exists *)
       | SOME (arch_ebpf (NONE)) =>
        (case get_arch_block_pbl_name (EL 0 ab_list') of
         | SOME pbl_name =>
          (case ALOOKUP pblock_map pbl_name of
           | SOME (pblock, argtys) =>
            SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, SOME (arch_ebpf (SOME (ebpf_pkg_ebpfFilter (EL 1 argtys)))), ab_list', action_list, extfun_list, ttymap)
           | _ => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Unknown programmable block in top-level package instantiation: "++pbl_name))
         | NONE => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Invalid block in top-level package instantiation"))
       | SOME (arch_ebpf _) =>
        NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Duplicate top-level package instantiations")
       (* V1Model: Only one top-level package exists *)
       | SOME (arch_v1model (NONE)) =>
        (case get_arch_block_pbl_name (EL 0 ab_list') of
         | SOME pbl_name =>
          (case ALOOKUP pblock_map pbl_name of
           | SOME (pblock, argtys) =>
            SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, SOME (arch_v1model (SOME (v1model_pkg_V1Switch (EL 1 argtys) (EL 2 argtys)))), ab_list', action_list, extfun_list, ttymap)
           | _ => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Unknown programmable block in top-level package instantiation: "++pbl_name))
         | NONE => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Invalid block in top-level package instantiation"))
       | SOME (arch_v1model _) =>
        NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Duplicate top-level package instantiations")

       | _ => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Unexpected top-level package instantiation"))
     | NONE_msg msg => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg)

   else NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) ("Unknown declaration element type: "++elem_name)

   (* TODO: ??? *)
  | _ => NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) "Unknown JSON format of element"
End

(* Note: Spec states "bit" is shorthand for bit<1> *)
(* TODO: Factor out this initial state to a constant term *)
Definition petr4_parse_elements_def:
 petr4_parse_elements json_list arch_pkg_opt =
  FOLDL ( \ res_opt json. case res_opt of
                     | SOME_dbg res => petr4_parse_element res json
                     | NONE_dbg data msg => NONE_dbg data msg) (SOME_dbg ([("bit", p_tau_bit 1)],[],[],[(funn_ext "header" "isValid",[],p_tau_bool); (funn_ext "header" "setValid",[],p_tau_bot); (funn_ext "header" "setInvalid",[],p_tau_bot)],[],[],[],[],[((^apply_result_placeholder_varn), (v_bot, NONE))],[],[],arch_pkg_opt,[],[],[],[])) json_list
End

(* Removes the list of arguments stored in pblock_map, which is only used during the
 * final step of parsing when inferring type arguments
 * Removes extfun_list and action_list *)
(* TODO: Do more stuff *)
Definition clean_result_def:
 clean_result res_msg =
  case res_msg of
  | SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) =>
   let (pblock_map', pblock_action_names_map) = p4_clean_pblock_map pblock_map ab_list in
   SOME_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, MAP (\ (key:string, (v1:pblock, v2:tau list)). (key, v1)) pblock_map', p4_clean_tbl_entries_map tbl_entries_map ab_list, arch_pkg_opt, ab_list, ttymap, pblock_action_names_map)
  | NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map, tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap) msg =>
   let (pblock_map', pblock_action_names_map) = p4_clean_pblock_map pblock_map ab_list in
   NONE_dbg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map', tbl_entries_map, arch_pkg_opt, ab_list, action_list, extfun_list, ttymap, pblock_action_names_map) msg
End

Definition p4_from_json_def:
(p4_from_json json_parse_result arch_pkg_opt =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
  dbg_remove $ clean_result $ petr4_parse_elements json_list arch_pkg_opt
 | NONE_msg msg => NONE_msg msg)
End

Definition pblock_get_tbl_map_def:
 pblock_get_tbl_map pblock =
  case pblock of
  | (pbl_type, params, b_func_map, decl_list, pars_map, tbl_map) => tbl_map
End

Definition ctrl_from_pblock_map_def:
 ctrl_from_pblock_map pblock_map =
  MAP (\ (k, v). pblock_get_tbl_map v) pblock_map
End

(**********************)
(* For the SML script *)

Definition p4_infer_arg_def:
 (p4_infer_arg [] = SOME []) /\
 (p4_infer_arg ((ty, v)::t) =
  case ty of
   | p_tau_bit n =>
    (case p4_infer_arg t of
     | SOME res =>
      SOME ((e_v (v_bit ((fixwidth n (n2v v), n))))::res)
     | NONE => NONE)
   | _ => NONE)
End

Definition p4_infer_args_def:
 (p4_infer_args (ftymap, blftymap) block_name action_name [] = SOME []) /\
 (p4_infer_args (ftymap, blftymap) block_name action_name args =
  case
   (case ALOOKUP blftymap block_name of
    | SOME local_ftymap =>
     (case ALOOKUP local_ftymap (funn_name action_name) of
      | SOME (arg_p_taus, ret_tau) =>
       p4_infer_arg (ZIP(arg_p_taus, args))
      | NONE => NONE)
    | NONE => NONE) of
   | SOME res => SOME res
   | NONE =>
    (case ALOOKUP ftymap (funn_name action_name) of
     | SOME (arg_p_taus, ret_tau) =>
      p4_infer_arg (ZIP(arg_p_taus, args))
     | NONE => NONE))
End

Definition p4_infer_key_def:
 (p4_infer_key [] = SOME []) /\
 (p4_infer_key ((ty, v)::t) =
  case ty of
   | tau_bit n =>
    (case p4_infer_key t of
     | SOME res =>
      SOME ((e_v (v_bit ((fixwidth n (n2v v), n))))::res)
     | NONE => NONE)
   | _ => NONE)
End

Definition p4_infer_keys_def:
 (p4_infer_keys ttymap table_name [] = SOME []) /\
 (p4_infer_keys ttymap table_name keys =
  (case ALOOKUP ttymap table_name of
   | SOME taus => p4_infer_key (ZIP(taus,keys))
   | NONE => NONE))
End

Definition init_ctrl_entry_gen_def:
 init_ctrl_entry_gen tbl_map (tbl_name, updates) =
  case ALOOKUP tbl_map tbl_name of
  | SOME tbl =>
   (* TODO: Note that this doesn't remove old table entries *)
   (* TODO: Double-check order of updates: This is critical. Last update must be first *)
   SOME (AUPDATE tbl_map (tbl_name, updates++tbl))
  | NONE => NONE
End

Definition init_ctrl_gen_def:
 init_ctrl_gen tbl_map name_upd_list =
  FOLDL (\map_opt upd. case map_opt of | SOME map => init_ctrl_entry_gen map upd | NONE => NONE) (SOME tbl_map) name_upd_list
End

Definition p4_pblock_of_tbl_def:
 p4_pblock_of_tbl tbl pblock_map =
  case (FIND (\ (pbl_name, pblock).
	      case pblock of
	      | (pbl_type, params, b_func_map, t_scope, pars_map, tbl_map) =>
	       (case ALOOKUP tbl_map tbl of
		| SOME res => T
		| NONE => F)) pblock_map) of
  | SOME (x,pbl) => SOME x
  | NONE => NONE
End

(* TODO: Move *)
Definition FILTER_DUPLICATES_def:
 (FILTER_DUPLICATES [] = []) /\
 (FILTER_DUPLICATES (h::t) =
  (h::(FILTER_DUPLICATES (FILTER ($<> h) t))))
Termination
WF_REL_TAC `measure LENGTH` >>
rpt strip_tac >>
ASSUME_TAC (Q.SPECL [`(\y. h <> y)`, `t`] rich_listTheory.LENGTH_FILTER_LEQ) >>
fs[prim_recTheory.LESS_THM]
End

(* TODO: Put in files with other arch-specific stuff? *)
(* Get initial mappings for ctrl from the programmable blocks map *)
Definition ebpf_init_ctrl_def:
 ebpf_init_ctrl pblock_map tbl_updates =
  let
   init_tbl_map = (FLAT (MAP (\ (pblock_name, pblock). case pblock of
                      | (pbl_type, params, b_func_map, decl_list, state_map, tbl_map) => ZIP ((MAP FST tbl_map), REPLICATE (LENGTH tbl_map) [])) pblock_map)):ebpf_ctrl
  in
  let
   init_tbl_map' = FILTER_DUPLICATES init_tbl_map
  in
   init_ctrl_gen init_tbl_map' tbl_updates
End

Definition vss_init_ctrl_def:
 vss_init_ctrl pblock_map tbl_updates =
  let
   init_tbl_map = (FLAT (MAP (\ (pblock_name, pblock). case pblock of
                      | (pbl_type, params, b_func_map, decl_list, state_map, tbl_map) =>
                       ZIP ((MAP FST tbl_map), REPLICATE (LENGTH tbl_map) [])) pblock_map)):vss_ctrl
  in
  let
   init_tbl_map' = FILTER_DUPLICATES init_tbl_map
  in
   init_ctrl_gen init_tbl_map' tbl_updates
End

Definition v1model_init_ctrl_def:
 v1model_init_ctrl pblock_map tbl_updates =
  let
   init_tbl_map = (FLAT (MAP (\ (pblock_name, pblock). case pblock of
                      | (pbl_type, params, b_func_map, decl_list, state_map, tbl_map) => ZIP ((MAP FST tbl_map), REPLICATE (LENGTH tbl_map) [])) pblock_map)):v1model_ctrl
  in
  let
   init_tbl_map' = FILTER_DUPLICATES init_tbl_map
  in
   init_ctrl_gen init_tbl_map' tbl_updates
End


(* Replaces the default action of a table. Used when parsing STF specifications *)
Definition p4_replace_tbl_default_def:
 p4_replace_tbl_default (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) block_name table_name action_name args =
  case ALOOKUP pblock_map block_name of
  | SOME (pbl_type_control, params, b_func_map, decl_list, ([]:pars_map), tbl_map) =>
   (case ALOOKUP tbl_map table_name of
    | SOME (mk_l, (old_action_name, old_args)) =>
     SOME (ab_list, AUPDATE pblock_map (block_name, (pbl_type_control, params, b_func_map, decl_list, ([]:pars_map), (AUPDATE tbl_map (table_name, (mk_l, (action_name, args)))))),
             ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
    | NONE => NONE)
  | _ => NONE
End


(*********)
(* TESTS *)

(*

(* CURRENT WIP *)

val wip_tm = stringLib.fromMLstring $ TextIO.inputAll $ TextIO.openIn "validation_tests/issue2170-bmv2.json";

val wip_parse_thm = EVAL ``parse (OUTL (lex (^wip_tm) ([]:token list))) [] T``;

(* More detailed debugging:
open petr4_to_hol4p4Syntax;

val wip_test_tm = dest_SOME_msg $ rhs $ concl $ EVAL ``p4_from_json_preamble ^(rhs $ concl wip_parse_thm)``;

(* The index of the list in wip_test_tm at where you want to start debugging
 * (note the correspondence with the usage below in p4_from_json_def) *)
val index_of_error = ``4:num``;

val wip_control_inst_tm = rhs $ concl $ EVAL ``EL (^index_of_error) ^wip_test_tm``;

(* Re-definition of p4_from_json that only converts up until index_of_error *)
Definition p4_from_json_def:
(p4_from_json json_parse_result arch_pkg_opt =
 case p4_from_json_preamble json_parse_result of
 | SOME_msg json_list =>
  (* TODO: Debug here by TAKE-ing different parts of the json_list *)
  petr4_parse_elements (TAKE (^index_of_error) json_list) arch_pkg_opt
 | NONE_msg msg => NONE_msg msg)
End

(* The object to be converted to HOL4P4 at index_of_error *)
val wip_obj = optionSyntax.dest_some $ rhs $ concl $ EVAL ``case (^wip_control_inst_tm) of | Array [String elem_name; obj] => SOME obj | _ => NONE``;

(* The result immediately prior to index_of_error, which gives us the debugging variables *)
val [wip_tyenv, wip_enummap, wip_vtymap, wip_ftymap, wip_blftymap, wip_fmap, wip_bltymap, wip_ptymap, wip_gscope, wip_pblock_map, wip_tbl_entries, wip_arch_pkg_opt, wip_ab_list, wip_action_list, wip_extfun_list, wip_ttymap] = pairSyntax.spine_pair $ dest_SOME_msg $ rhs $ concl $ EVAL ``p4_from_json ^(rhs $ concl wip_parse_thm) (SOME (arch_v1model (NONE)))``;

(***********************************************)

(* MANUAL DEBUG: From here on, start by choosing sub-case of petr4_parse_element *)
EVAL ``petr4_parse_element (^wip_tyenv, ^wip_enummap, ^wip_vtymap, ^wip_ftymap, ^wip_blftymap, ^wip_fmap, ^wip_bltymap, ^wip_ptymap, ^wip_gscope, ^wip_pblock_map, ^wip_tbl_entries, ^wip_arch_pkg_opt, ^wip_ab_list, ^wip_action_list, ^wip_extfun_list, ^wip_ttymap) ^wip_control_inst_tm``;

EVAL ``petr4_parse_actiondef (^wip_tyenv, ^wip_enummap, ^wip_vtymap, ^wip_ftymap, ^wip_fmap, ^wip_gscope, ^wip_action_list, ^wip_extfun_list) ^wip_obj``

EVAL ``petr4_fun_to_fmapupdate (^wip_tyenv, ^wip_enummap, ^wip_vtymap, ^wip_ftymap, ^wip_fmap, ^wip_gscope, [], ^wip_action_list, ^wip_extfun_list) ^wip_obj funtype_action``

EVAL ``ALL_DISTINCT ((^apply_result_placeholder)::(MAP FST [("from_table",d_in); ("hit",d_in)]))``

EVAL ``add_apply_result_inline (^wip_action_list++["NoAction"]) (add_explicit_return stmt_empty) "NoAction"``

EVAL ``replace_action_args (stmt_seq
          (stmt_cond (e_var (varn_name "from_table"))
             (stmt_ass (lval_varname (varn_name "gen_apply_result"))
                (e_struct
                   [("hit",e_var (varn_name "hit"));
                    ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                    ("action_run",
                     e_v
                       (v_bit
                          ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                            F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],
                           32)))])) stmt_empty)
          (stmt_seq stmt_empty (stmt_ret (e_v v_bot)))) ^wip_action_list``


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
