open HolKernel boolLib Parse bossLib ottLib;

open p4Theory;

val _ = new_theory "p4_core";

(*****************)
(* core ext type *)
(*****************)

val _ = Hol_datatype ` 
core_v_ext =
   core_v_ext_packet_in of (bool list)
 | core_v_ext_packet_out of (bool list)`;

(* TODO: Definitions with _gen get specialised later by the different architectures *)

(******************)
(* Header methods *)
(******************)

Definition min_size_in_bits:
 (min_size_in_bits (v_header valid_bit []) = SOME 0) /\
 (min_size_in_bits (v_header valid_bit (h::t)) =
  case SND h of
  | (v_bit (bl, num)) => 
   (case min_size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v_bool _) =>
   (case min_size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | _ => NONE
 )
End

Definition min_size_in_bytes:
 (min_size_in_bytes (v_header valid_bit x_v_l) =
  case min_size_in_bits (v_header valid_bit x_v_l) of
  | SOME num => SOME ((num+7) DIV 8)
  | NONE => NONE
 )
End

Definition header_is_valid:
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (let scope_list' = initialise scope_list varn_ext_ret (v_bool valid_bit) in
    SOME (ascope, g_scope_list, scope_list'))
  | _ => NONE
 )
End

Definition header_set_valid:
 (header_set_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scope_list (v_header T x_v_l) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME (ascope, g_scope_list, scope_list')
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
     SOME (ascope, g_scope_list, scope_list')
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

Definition update_ascope_gen:
 (update_ascope_gen ascope_update (ascope:'a) (ext_ref:num) (v_ext:(core_v_ext, 'b) sum) =
  ascope_update ascope ext_ref v_ext
 )
End

Definition lookup_lval_header:
 (lookup_lval_header ss header_lval =
  case lookup_lval ss header_lval of
   | SOME (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

(* Helper function to extract *)
Definition set_header_fields':
 (set_header_fields' []     acc _ = SOME acc) /\
 (set_header_fields' (h::t) acc packet_in =
  case h of
  | (x:x, (v_bool b)) => set_header_fields' t ((x, (v_bool (HD packet_in)))::acc) (DROP 1 packet_in)
  | (x, (v_bit (bv, l))) => set_header_fields' t ((x, (v_bit (TAKE l packet_in, l)))::acc) (DROP l packet_in)
  | _ => NONE
 )
End
Definition set_header_fields:
 (set_header_fields x_v_l packet_in = set_header_fields' x_v_l [] packet_in)
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover extraction to header stacks *)
(* Note the usage of "REVERSE" to keep the order of fields in the header the same *)
Definition packet_in_extract_gen:
 (packet_in_extract_gen ascope_lookup ascope_update (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_header scope_list (lval_varname (varn_name "hdr")) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet_in packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case min_size_in_bits (v_header valid_bit x_v_l) of
        | SOME size =>
         if size <= LENGTH packet_in_bl
         then
          (case set_header_fields x_v_l packet_in_bl of
           | SOME x_v_l' =>
            (case assign scope_list (v_header T (REVERSE x_v_l')) (lval_varname (varn_name "hdr")) of
             | SOME scope_list' =>
              SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet_in (DROP size packet_in_bl))):(core_v_ext, 'b) sum), g_scope_list, scope_list')
             | NONE => NONE)
           | NONE => NONE)
         else
          (case assign scope_list (v_err "PacketTooShort") (lval_varname (varn_name "parseError")) of
           | SOME scope_list' => SOME (ascope, g_scope_list, scope_list')
           | NONE => NONE)
        | NONE => NONE)
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
  | v_struct [] => SOME []
  | v_struct (h'::t') =>
   (case flatten_v_l [SND h'] of
    | SOME l =>
     (case flatten_v_l ((v_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v_bit (bl, n) => SOME bl
  | v_bool b => SOME [b]
  | _ => NONE
 )
End

(* TODO: Should also support emission from: header stack and header union *)
(* Note: Nested headers are not allowed, so this is only checked at top level *)
Definition packet_out_emit_gen:
 (packet_out_emit_gen ascope_lookup ascope_update (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_ascope_gen ascope_lookup ascope i of
    | SOME (INL (core_v_ext_packet_out packet_out_bl)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "data")) of
      | SOME (v_header F x_v_l) => SOME (ascope, g_scope_list, scope_list)
      | SOME (v_header T x_v_l) =>
       (case flatten_v_l (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet_out (packet_out_bl++bl))):(core_v_ext, 'b) sum), g_scope_list, scope_list)
        | NONE => NONE)
      | SOME (v_struct x_v_l) =>
       (case flatten_v_l (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet_out (packet_out_bl++bl))):(core_v_ext, 'b) sum), g_scope_list, scope_list)
        | NONE => NONE)
      | SOME _ => NONE
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

val _ = export_theory ();
