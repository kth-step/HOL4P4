open HolKernel boolLib Parse bossLib ottLib;

open p4Theory;

val _ = new_theory "p4_core";

(******************)
(* Header methods *)
(******************)

(* We might want this to take a header argument to agree with minSizeInBits() *)
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
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scopes_stack) =
  case lookup_lval scopes_stack (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (let scopes_stack' = initialise scopes_stack varn_ext_ret (v_bool valid_bit) in
    SOME (ascope, g_scope_list, scopes_stack'))
  | _ => NONE
 )
End

Definition header_set_valid:
 (header_set_valid (g_scope_list:g_scope_list, scopes_stack) =
  case lookup_lval scopes_stack (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scopes_stack (v_header T x_v_l) (lval_varname (varn_name "this")) of
    | SOME scopes_stack' =>             
     SOME (g_scope_list, scopes_stack')
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid:
 (header_set_invalid (g_scope_list:g_scope_list, scopes_stack) =
  case lookup_lval scopes_stack (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scopes_stack (v_header F x_v_l) (lval_varname (varn_name "this")) of
    | SOME scopes_stack' =>             
     SOME (g_scope_list, scopes_stack')
    | NONE => NONE)
  | _ => NONE
 )
End

(*********************)
(* packet_in methods *)
(*********************)

(* TODO: Fix this
Definition lookup_packet_in:
 (lookup_packet_in ss ext_obj_name =
  case lookup_lval ss ext_obj_name of
  | SOME (v_ext (ext_obj_in packet_in)) => SOME packet_in
  | _ => NONE
 )
End
*)

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
(* TODO: Fix this
Definition packet_in_extract:
 (packet_in_extract (g_scope_list:g_scope_list, scopes_stack, ctrl:ctrl) =
  case lookup_packet_in scopes_stack (lval_varname (varn_name "this")) of
  | SOME packet_in =>
   (case lookup_lval_header scopes_stack (lval_varname (varn_name "hdr")) of
    | SOME (valid_bit, x_v_l) =>
     (case min_size_in_bits (v_header valid_bit x_v_l) of
      | SOME size =>
       if size <= LENGTH packet_in
       then
        (case set_header_fields x_v_l packet_in of
         | SOME x_v_l' =>
          (case assign scopes_stack (v_header T (REVERSE x_v_l')) (lval_varname (varn_name "hdr")) of
           | SOME scopes_stack' =>
           (case assign scopes_stack' (v_ext (ext_obj_in (DROP size packet_in))) (lval_varname (varn_name "this")) of
            | SOME scopes_stack'' =>
             SOME (g_scope_list, scopes_stack'', ctrl)
            | NONE => NONE)
           | NONE => NONE)
         | NONE => NONE)
       else
        (case assign scopes_stack (v_err "PacketTooShort") (lval_varname (varn_name "parseError")) of
         | SOME scopes_stack' => SOME (g_scope_list, scopes_stack', ctrl)
         | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | NONE => NONE
 )
End
*)

(**********************)
(* packet_out methods *)
(**********************)

(* TODO: Fix the packet_in/packet_out hack *)
(* TODO: Fix this
Definition lookup_packet_out:
 (lookup_packet_out frame ext_obj_name =
  case lookup_lval frame ext_obj_name of
  | SOME (v_ext (ext_obj_out packet_out)) => SOME packet_out
  | SOME (v_ext (ext_obj_in packet_out)) => SOME packet_out
  | _ => NONE
 )
End
*)

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
(* TODO: Fix this
Definition packet_out_emit:
 (packet_out_emit (g_scope_list:g_scope_list, scopes_stack, ctrl:ctrl) =
  case lookup_packet_out scopes_stack (lval_varname (varn_name "this")) of
  | SOME packet_out =>
   (case lookup_lval scopes_stack (lval_varname (varn_name "data")) of
    | SOME (v_header F x_v_l) => SOME (g_scope_list, scopes_stack, ctrl)
    | SOME (v_header T x_v_l) =>
     (case flatten_v_l (MAP SND x_v_l) of
      | SOME bl =>
       (case assign scopes_stack (v_ext (ext_obj_out (packet_out++bl))) (lval_varname (varn_name "this")) of
	| SOME scopes_stack' =>             
	 SOME (g_scope_list, scopes_stack', ctrl)
	| NONE => NONE)
      | NONE => NONE)
    | SOME (v_struct x_v_l) =>
     (case flatten_v_l (MAP SND x_v_l) of
      | SOME bl =>
       (case assign scopes_stack (v_ext (ext_obj_out (packet_out++bl))) (lval_varname (varn_name "this")) of
	| SOME scopes_stack' =>             
	 SOME (g_scope_list, scopes_stack', ctrl)
	| NONE => NONE)
      | NONE => NONE)
    | SOME _ => NONE
    | NONE => NONE)
  | NONE => NONE)
End
*)

val _ = export_theory ();
