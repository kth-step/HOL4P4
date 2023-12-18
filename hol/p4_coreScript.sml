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
val _ = Hol_datatype ` 
core_v_ext =
   core_v_ext_packet of (bool list)`;

(* NOTE: Definitions with _gen get specialised later by the different architectures *)

(**********************)
(* Objectless methods *)
(**********************)

Definition verify_gen:
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
Definition size_in_bytes:
 (size_in_bytes (v_header valid_bit x_v_l) =
  case size_in_bits (v_header valid_bit x_v_l) of
  | SOME num => SOME ((num+7) DIV 8)
  | NONE => NONE
 )
End

Definition header_is_valid:
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status_returnv (v_bool valid_bit))
  | _ => NONE
 )
End

Definition header_set_valid:
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

Definition header_set_invalid:
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

Definition lookup_ascope_gen:
 (lookup_ascope_gen ascope_lookup (ascope:'a) (ext_ref:num) =
  case ascope_lookup ascope ext_ref of
  | SOME v_ext => SOME (v_ext:(core_v_ext, 'b) sum)
  | _ => NONE
 )
End

(* TODO: Is this really needed as a separate function? *)
Definition update_ascope_gen:
 (update_ascope_gen ascope_update (ascope:'a) (ext_ref:num) (v_ext:(core_v_ext, 'b) sum) =
  (ascope_update ascope ext_ref v_ext):'a
 )
End

Definition lookup_lval_header:
 (lookup_lval_header ss header_lval =
  case lookup_lval ss header_lval of
   | SOME (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

(* Partial, but does the job where it is used *)
Definition set_bool:
 (set_bool packet_in = v_bool (HD packet_in))
End
Definition set_bit:
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

Definition set_header:
 (set_header x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_header T x_v_l')
  | NONE => NONE)
End

Definition set_struct:
 (set_struct x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_struct x_v_l')
  | NONE => NONE)
End

Definition set_v:
 (set_v (v_bit (bitv, n)) packet_in = SOME (set_bit n packet_in)) /\
 (set_v (v_bool b)        packet_in = SOME (set_bool packet_in)) /\
 (set_v (v_struct x_v_l)  packet_in = (set_struct x_v_l packet_in)) /\
 (set_v (v_header validity x_v_l) packet_in = (set_header x_v_l packet_in))
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover extraction to header stacks *)
Definition packet_in_extract_gen:
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
Definition packet_in_lookahead_gen:
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

Definition lookup_lval_bit32:
 (lookup_lval_bit32 ss bit32_lval =
  case lookup_lval ss bit32_lval of
   | SOME (v_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End

Definition packet_in_advance_gen:
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

Definition flatten_v_l:
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
Definition packet_out_emit_gen:
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

(* For use in table matching *)
Definition AFIND_PRED_def:
 AFIND_PRED l k =
  case FIND (\ (set, _). set k) l of
  | SOME (_, act_args) => SOME act_args
  | NONE => NONE
End

val _ = export_theory ();
