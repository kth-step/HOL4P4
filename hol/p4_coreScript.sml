open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory;

val _ = new_theory "p4_core";

(*****************)
(* core ext type *)
(*****************)

(* TODO: Separate packet_in and packet_out?  *)

(* packet_in:
     https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-packet-data-extraction
*)
Datatype:
 core_v_ext =
  core_v_ext_packet (bool list)
End

(* NOTE: Definitions with _gen get specialised later by the different architectures *)

(**********************)
(* Objectless methods *)
(**********************)

Definition verify_gen_def:
 (verify_gen ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "condition")) of
  | SOME (v_bool T) =>
   SOME (ascope, scope_list, status_returnv v_bot)
  | SOME (v_bool F) =>
   (case lookup_lval scope_list (lval_varname (varn_name "err")) of
    | SOME (v_bit bitv) =>
     SOME (ascope_update_v_map ascope "parseError" (v_bit bitv), scope_list, status_trans "reject")
    | _ => NONE)
  | _ => NONE
 )
End

(******************)
(* Header methods *)
(******************)

(* TODO: Perform this on list only? *)
(* NOTE: This features more types that we can actually extract to, to facilitate re-use *)
Definition size_in_bits_def:
 (size_in_bits (v_bool b) = SOME 1) /\
 (size_in_bits (v_bit (bl, n)) = SOME n) /\
 (size_in_bits (v_header valid_bit []) = SOME 0) /\
 (size_in_bits (v_struct []) = SOME 0) /\
 (size_in_bits (v_header valid_bit (h::t)) =
  case SND h of
  | (v_bit (bl, num)) =>
   (case size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v_bool _) =>
   (case size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | (v_struct fields) =>
   (case size_in_bits (v_header valid_bit t) of
    | SOME num' =>
     (case size_in_bits (v_struct fields) of
      | SOME num'' =>
       SOME (num'' + num')
      | NONE => NONE
     )
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits (v_struct (h::t)) =
  case SND h of
  | (v_bit (bl, num)) => 
   (case size_in_bits (v_struct t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v_bool _) =>
   (case size_in_bits (v_struct t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits _ = NONE)
End

(* TODO: Perform this on list only? *)
Definition size_in_bytes_def:
 (size_in_bytes (v_header valid_bit x_v_l) =
  case size_in_bits (v_header valid_bit x_v_l) of
  | SOME num => SOME ((num+7) DIV 8)
  | NONE => NONE
 )
End

Definition header_is_valid_def:
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status_returnv (v_bool valid_bit))
  | _ => NONE
 )
End

Definition header_set_valid_def:
 (header_set_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scope_list (v_header T x_v_l) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid_def:
 (header_set_invalid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scope_list (v_header F x_v_l) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>             
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End


(*********************)
(* packet_in methods *)
(*********************)

Definition lookup_ascope_gen_def:
 (lookup_ascope_gen ascope_lookup (ascope:'a) (ext_ref:num) =
  case ascope_lookup ascope ext_ref of
  | SOME v_ext => SOME (v_ext:(core_v_ext, 'b) sum)
  | _ => NONE
 )
End

(* TODO: Is this really needed as a separate function? *)
Definition update_ascope_gen_def:
 (update_ascope_gen ascope_update (ascope:'a) (ext_ref:num) (v_ext:(core_v_ext, 'b) sum) =
  (ascope_update ascope ext_ref v_ext):'a
 )
End

Definition lookup_lval_header_def:
 (lookup_lval_header ss header_lval =
  case lookup_lval ss header_lval of
   | SOME (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

(* Partial, but does the job where it is used *)
Definition set_bool_def:
 (set_bool packet_in = v_bool (HD packet_in))
End
Definition set_bit_def:
 (set_bit n packet_in = v_bit (TAKE n packet_in, n))
End

Definition set_fields_def:
 (set_fields []     acc _ = SOME acc) /\
 (set_fields (h::t) acc packet_in =
  case h of
  | (x:x, (v_bool b)) => set_fields t (acc++[(x, set_bool packet_in)]) (DROP 1 packet_in)
  | (x, (v_bit (bv, l))) => set_fields t (acc++[(x, set_bit l packet_in)]) (DROP l packet_in)
  | (x, (v_struct x_v_l)) =>
   (case size_in_bits (v_struct x_v_l) of
    | SOME n =>
     (case set_fields x_v_l [] (TAKE n packet_in) of
      | SOME acc' =>
       set_fields t (acc++[(x, v_struct acc')]) (DROP n packet_in)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE)
Termination
WF_REL_TAC `measure ( \ (t, acc, packet_in). v1_size t)`
End

Definition set_header_def:
 (set_header x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_header T x_v_l')
  | NONE => NONE)
End

Definition set_struct_def:
 (set_struct x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_struct x_v_l')
  | NONE => NONE)
End

Definition set_v_def:
 (set_v (v_bit (bitv, n)) packet_in = SOME (set_bit n packet_in)) /\
 (set_v (v_bool b)        packet_in = SOME (set_bool packet_in)) /\
 (set_v (v_struct x_v_l)  packet_in = (set_struct x_v_l packet_in)) /\
 (set_v (v_header validity x_v_l) packet_in = (set_header x_v_l packet_in))
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover extraction to header stacks *)
Definition packet_in_extract_gen_def:
 (packet_in_extract_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_header scope_list (lval_varname (varn_name "headerLvalue")) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits (v_header valid_bit x_v_l) of
        | SOME size =>
         if size <= LENGTH packet_in_bl
         then
          (case set_header x_v_l packet_in_bl of
           | SOME header =>
            (case assign scope_list header (lval_varname (varn_name "headerLvalue")) of
             | SOME scope_list' =>
              SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP size packet_in_bl))):(core_v_ext, 'b) sum), scope_list', status_returnv v_bot)
             | NONE => NONE)
           | NONE => NONE)
         else
          (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet [])):(core_v_ext, 'b) sum)) "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject")
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-packet-lookahead *)
Definition packet_in_lookahead_gen_def:
 (packet_in_lookahead_gen ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval scope_list (lval_varname (varn_name "targ1")) of
    | SOME dummy_v =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits dummy_v of
        | SOME size =>
         if size <= LENGTH packet_in_bl
         then
          (case set_v dummy_v packet_in_bl of
           | SOME v =>
            SOME (ascope, scope_list, status_returnv v)
           | NONE => NONE)
         else
          (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map ascope "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject")
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

(* Advance
   https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-skip-bits
*)

Definition lookup_lval_bit32_def:
 (lookup_lval_bit32 ss bit32_lval =
  case lookup_lval ss bit32_lval of
   | SOME (v_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End

Definition packet_in_advance_gen_def:
 (packet_in_advance_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_bit32 scope_list (lval_varname (varn_name "bits")) of
    | SOME n_bits =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       if n_bits <= LENGTH packet_in_bl
       then
        SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP n_bits packet_in_bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
       else
        (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
        SOME (ascope_update_v_map ascope "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject")
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End


(**********************)
(* packet_out methods *)
(**********************)

Definition flatten_v_l_def:
 (flatten_v_l [] = SOME []) /\
 (flatten_v_l (h::t) =
  case h of
  | v_struct [] =>
   (case flatten_v_l t of
    | SOME l => SOME l
    | NONE => NONE)
  | v_struct (h'::t') =>
   (case flatten_v_l [SND h'] of
    | SOME l =>
     (case flatten_v_l ((v_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v_header validity [] =>
   (case flatten_v_l t of
    | SOME l => SOME l
    | NONE => NONE)
  | v_header validity (h'::t') =>
   (case flatten_v_l [SND h'] of
    | SOME l =>
     (case flatten_v_l ((v_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v_bit (bl, n) =>
   (case flatten_v_l t of
    | SOME l => SOME (bl++l)
    | NONE => NONE)
  | v_bool b =>
   (case flatten_v_l t of
    | SOME l => SOME (b::l)
    | NONE => NONE)
  | _ => NONE
 )
End

(* TODO: Should also support emission from: header stack and header union *)
(* Note: Nested headers are not allowed, so this is only checked at top level *)
Definition packet_out_emit_gen_def:
 (packet_out_emit_gen (ascope_lookup:'a -> num -> (core_v_ext + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_ascope_gen ascope_lookup ascope i of
    | SOME (INL (core_v_ext_packet packet_out_bl)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "data")) of
      | SOME (v_header F x_v_l) => SOME (ascope, scope_list, status_returnv v_bot)
      | SOME (v_header T x_v_l) =>
       (case flatten_v_l (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        | NONE => NONE)
      | SOME (v_struct x_v_l) =>
       (case flatten_v_l (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        | NONE => NONE)
      | SOME _ => NONE
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(************)
(* Checksum *)
(************)

Definition header_entries2v_def:
 (header_entries2v [] = SOME []) /\
 (header_entries2v (h::t) =
  case header_entry2v h of
  | SOME bl =>
  (case header_entries2v t of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 ) /\
 (header_entry2v (x:x, v) =
  case v of
  | (v_bit (bl, n)) => SOME bl
  | (v_struct x_v_l) => header_entries2v x_v_l
  | (v_header validity x_v_l) => header_entries2v x_v_l
  | _ => NONE
 )
Termination
WF_REL_TAC `measure ( \ t. case t of | (INL x_v_l) => v1_size x_v_l | (INR (x,v)) => v_size v)`
End


Definition v2w16s'_def:
 (v2w16s' [] = []) /\
 (v2w16s' v =
  ((v2w (TAKE 16 v)):word16)::(v2w16s' (DROP 16 v))
 )
Termination
WF_REL_TAC `measure LENGTH` >>
fs []
End

Definition v2w16s_def:
 (v2w16s v = if (LENGTH v) MOD 16 = 0 then SOME (v2w16s' v) else NONE)
End

Definition get_checksum_incr_def:
 (get_checksum_incr scope_list ext_data_name =
   (case lookup_lval scope_list ext_data_name of
    | SOME (v_bit (bl, n)) =>
     if n MOD 16 = 0 then SOME (v2w16s' bl) else NONE
    | SOME (v_header vbit f_list) =>
     (case header_entries2v f_list of
      | SOME bl => v2w16s bl
      | NONE => NONE)
    | SOME (v_struct f_list) =>
     (case header_entries2v f_list of
      | SOME bl => v2w16s bl
      | NONE => NONE)
    | _ => NONE)
 )
End

(* Alternative version tailored for symbolic execution *)
Definition get_checksum_incr'_def:
 (get_checksum_incr' scope_list ext_data_name =
   (case lookup_lval scope_list ext_data_name of
    | SOME (v_bit (bl, n)) =>
     if n MOD 16 = 0 then SOME bl else NONE
    | SOME (v_header vbit f_list) =>
     (case header_entries2v f_list of
      | SOME bl =>
       if (LENGTH bl) MOD 16 = 0 then SOME bl else NONE
      | NONE => NONE)
    | SOME (v_struct f_list) =>
     (case header_entries2v f_list of
      | SOME bl =>
       if (LENGTH bl) MOD 16 = 0 then SOME bl else NONE
      | NONE => NONE)
    | _ => NONE)
 )
End

Definition add_ones_complement_def:
 add_ones_complement (x, y) = 
  let
   (result,carry_out,overflow) = add_with_carry(x,y,F)
  in
   if carry_out
   then result + 1w
   else result
End

Definition sub_ones_complement_def:
 sub_ones_complement (x, y) =
   let
    (result,carry_out,overflow) = add_with_carry(x, word_1comp y,F)
   in
    if carry_out
    then result + 1w
    else word_1comp result
End

Definition compute_checksum16_def:
 compute_checksum16 (w16_list:word16 list) = 
  word_1comp (FOLDR (CURRY add_ones_complement) (0w:word16) w16_list)
End

Definition get_bitlist_def:
 get_bitlist scope_list ext_data_name =
  case lookup_lval scope_list ext_data_name of
   | SOME (v_bit (bl, n)) => SOME bl
   | SOME (v_header vbit f_list) =>
    (case header_entries2v f_list of
     | SOME bl => SOME bl
     | NONE => NONE)
   | SOME (v_struct f_list) =>
    (case header_entries2v f_list of
     | SOME bl => SOME bl
     | NONE => NONE)
   | _ => NONE
End


(*****************)
(* Architectural *)
(*****************)

(* TODO: Remove these and keep "v_map" as just a regular scope? *)
Definition v_map_to_scope_def:
 (v_map_to_scope [] = []) /\
 (v_map_to_scope (((k, v)::t):(string, v) alist) =
  ((varn_name k, (v, NONE:lval option))::v_map_to_scope t)
 )
End

Definition scope_to_vmap_def:
 (scope_to_vmap [] = SOME []) /\
 (scope_to_vmap ((vn, (v:v, lval_opt:lval option))::t) =
  case vn of
   | (varn_name k) => oCONS ((k, v), scope_to_vmap t)
   | _ => NONE
 )
End

Definition copyout_pbl_gen_def:
 copyout_pbl_gen xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope v_map in
   update_return_frame xlist dlist [v_map_scope] g_scope_list
End

(* A separate definition so that symbolic execution can choose to not evaluate it
 * and rewrite with assumptions instead *)
Definition get_port_number_def:
 get_port_number bl = v2n bl
End

(************************************)
(* Miscellaneous common definitions *)
(************************************)

(*
(* For use in table matching *)
Definition AFIND_PRED_def:
 AFIND_PRED l k =
  case FIND (\ (set, _). set k) l of
  | SOME (_, act_args) => SOME act_args
  | NONE => NONE
End
*)
(*
(* TODO: Do all this sorting once and for all before the program starts,
 * then make it the responsibility of the control plane to update the
 * table with the right format
 *
 * Current solution is crazy stupid hack with same signatures as before *)

(* New table matching algorithm tailored for symbolic execution:
   1. Sort by priority: insert every entry in new list as soon as
      entry of higher priority is encountered, before that entry.
      Flip depending on which priority implementation is being modeled.
   2. Just iterate through the result without bothering to keep track about priority.
*)

Definition insert_def:
 (insert f e [] = [e]) /\
 (insert f ((k,prio),v) (((k',prio'),v')::t) =
  if f prio prio'
  then (((k,prio),v)::(((k',prio'),v')::t))
  else (((k',prio'),v')::(insert f ((k,prio),v) t)))
End

(* TODO: None never wins, but should not even exist in this list *)
Definition insert_largest_prio_def:
 insert_largest_prio e l = insert (\ p:num p'. p > p') e l
End

Definition insert_smallest_prio_def:
 insert_smallest_prio e l = insert (\ p:num p'. p < p') e l
End

(* TODO: dumb sorting algorithm? *)
Definition sort_table_def:
 (sort_table f acc [] = acc) /\
 (sort_table f acc (h::t) =
  sort_table f (f h acc) t)
End

(* Simplest possible "Inner kernel" of matching that is meant
 * to be rewritten using path condition *)
Definition FOLDL_MATCH_symb_exec_def:
 (FOLDL_MATCH_symb_exec e_l res [] = res) /\
 (FOLDL_MATCH_symb_exec e_l res_act (((k,p),v)::t) =
  if k e_l
  then FOLDL_MATCH_symb_exec e_l v t
  else FOLDL_MATCH_symb_exec e_l res_act t)
End

Definition FOLDL_MATCH_def:
 FOLDL_MATCH e_l (res:(string # e list) # (num option)) entries =
  let entries' = sort_table insert_largest_prio [] entries in
   (FOLDL_MATCH_symb_exec e_l ((\ ((a,b),c). (a,b)) res) entries', NONE:num option)
End
*)

(* TODO: Are match_kinds needed at all in the dynamic semantics? *)
Definition FOLDL_MATCH_def:
 (FOLDL_MATCH e_l res [] = res) /\
 (FOLDL_MATCH e_l (res_act, res_prio_opt:num option) (((k,prio),v)::t) =
  if k e_l
  then
   (* TODO: Largest priority wins (like for P4Runtime API) is hard-coded *)
   case res_prio_opt of
   | SOME res_prio =>
    if prio > res_prio
    then
     FOLDL_MATCH e_l (v, SOME prio) t
    else FOLDL_MATCH e_l (res_act, res_prio_opt) t
   | NONE => FOLDL_MATCH e_l (v, SOME prio) t
  else FOLDL_MATCH e_l (res_act, res_prio_opt) t)
End

(*
Definition update_prios_def:
 (update_prios acc [] = []) /\
 (update_prios acc (((k,prio),v)::t) =
  let prio' = if prio = (0:num) then acc else prio in
   (((k,prio'),v)::(update_prios (acc+1) t)))
End

Definition FOLDL_MATCH_alt_def:
 FOLDL_MATCH_alt e_l (res:(string # e list) # (num option)) n entries =
  let entries' = update_prios n entries in
  let entries'' = sort_table insert_smallest_prio [] entries' in
   (FOLDL_MATCH_symb_exec e_l ((\ ((a,b),c). (a,b)) res) entries'', NONE:num option)
End
*)

(* Alternative version, which uses smallest priority *)
Definition FOLDL_MATCH_alt_def:
 (FOLDL_MATCH_alt e_l res acc [] = res) /\
 (FOLDL_MATCH_alt e_l (res_act, res_prio_opt:num option) acc (((k,prio),v)::t) =
  if k e_l
  then
   (* TODO: Smallest priority wins (like for TDI) is hard-coded,
    *       other than priority zero. *)
   case res_prio_opt of
   | SOME res_prio =>
    let prio' = if (prio = 0) then acc else prio in
    if (prio' < res_prio)
    then
     FOLDL_MATCH_alt e_l (v, SOME prio') (acc+1) t
    else FOLDL_MATCH_alt e_l (res_act, res_prio_opt) (acc+1) t
   | NONE => FOLDL_MATCH_alt e_l (v, SOME prio) (acc+1) t
  else FOLDL_MATCH_alt e_l (res_act, res_prio_opt) (acc+1) t)
End

val _ = export_theory ();
