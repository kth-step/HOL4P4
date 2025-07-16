open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_arch";
(* TODO: Remove? Almost nothing from here... *)

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
(*
open p4Theory p4_auxTheory p4_cake_auxLib p4_cake_auxTheory p4_cake_exec_semTheory;

open p4_retrofit_auxLib;

open blahhhh;
*)
open p4Theory p4_auxTheory p4_retrofit_auxLib;
open p4_coreTheory p4_v1modelTheory;

(*********************)
(* Core architecture *)

(*
Definition header_entries2v_def:
 (header_entries2v (INL []) = SOME []) /\
 (header_entries2v (INL (h::t)) =
  case header_entries2v (INR h) of
  | SOME bl =>
  (case header_entries2v (INL t) of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 ) /\
 (header_entries2v (INR (x, v)) =
  case v of
  | (v_bit (bl, n)) => SOME bl
  | (v_struct x_v_l) => header_entries2v (INL x_v_l)
  | (v_header validity x_v_l) => header_entries2v (INL x_v_l)
  | _ => NONE
 )
End
*)
(* Use regular ones
(* TODO: Where's this used? *)
Definition get_checksum_incr_def:
 (get_checksum_incr (scope_list:scope_list) ext_data_name =
   (case lookup_lval' scope_list ext_data_name of
    | SOME (v_bit (bl, n)) =>
     if n MOD 16 = 0 then (v2w16s''' bl) else NONE
    | SOME (v_header vbit f_list) =>
     (case header_entries2v (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | SOME (v_struct f_list) =>
     (case header_entries2v (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | _ => NONE)
 )
End

(** Some new architectural functions **)
(*
Definition v_map_to_scope_def:
 (v_map_to_scope [] = []) /\
 (v_map_to_scope (((k, v)::t)) =
  ((varn_name k, (v:v, NONE:lval option))::v_map_to_scope t))
End

Definition scope_to_vmap_def:
 (scope_to_vmap [] = SOME []) /\
 (scope_to_vmap ((vn, (v:v, lval_opt:lval option))::t) =
  case vn of
   | (varn_name k) => oCONS ((k, v), scope_to_vmap t)
   | _ => NONE)
End

Definition copyout_pbl_gen_def:
 copyout_pbl_gen xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope v_map in
   update_return_frame xlist dlist [v_map_scope] g_scope_list
End
*)

(** Generic implementations **)
Definition verify_gen_def:
 (verify_gen ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "condition"))) of
  | SOME (v_bool T) =>
   SOME (ascope, scope_list, status_returnv v_bot)
  | SOME (v_bool F) =>
   (case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "err"))) of
    | SOME (v_bit bitv) =>
     SOME (ascope_update_v_map ascope ^(get_id "parseError") (v_bit bitv), scope_list, status_trans ^(get_id "reject"))
    | _ => NONE)
  | _ => NONE
 )
End

Definition lookup_lval_header_def:
 (lookup_lval_header ss header_lval =
  case lookup_lval' ss header_lval of
   | SOME (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

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
  | (v_struct flds) =>
   (case size_in_bits (v_header valid_bit t) of
    | SOME num' =>
     (case size_in_bits (v_struct flds) of
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

Definition set_bool_def:
 (set_bool [] = NONE) /\
 (set_bool packet_in = SOME (v_bool (HD packet_in), TL packet_in))
End
Definition set_bit_def:
 (set_bit n packet_in =
  case oTAKE n packet_in of
  | SOME res => SOME (v_bit (res, n), DROP n packet_in)
  | NONE => NONE)
End

Definition set_fields_def:
 (set_fields []     acc _ = SOME acc) /\
 (set_fields (h::t) acc packet_in =
  case h of
  | (x:string, (v_bool b)) =>
   (case set_bool packet_in of
    | SOME (res, t') => set_fields t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v_bit (bv, l))) =>
   (case set_bit l packet_in of
    | SOME (res, t') => set_fields t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v_struct x_v_l)) =>
   (case size_in_bits (v_struct x_v_l) of
    | SOME n =>
     (case oTAKE_DROP n packet_in of
      | SOME (res, t') =>
       (case set_fields x_v_l [] res of
        | SOME acc' =>
         set_fields t (acc++[(x, v_struct acc')]) t'
        | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE)
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
 (set_v (v_bit (bitv, n)) packet_in =
  case set_bit n packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v (v_bool b)        packet_in =
  case set_bool packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v (v_struct x_v_l) packet_in = (set_struct x_v_l packet_in)) /\
 (set_v (v_header validity x_v_l) packet_in = (set_header x_v_l packet_in)) /\
 (set_v _ packet_in = NONE)
End



Definition packet_in_extract_gen_def:
 (packet_in_extract_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_header scope_list (lval_varname (varn_name ^(get_id "headerLvalue"))) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits (v_header valid_bit x_v_l) of
        | SOME sz =>
           if sz <= LENGTH packet_in_bl
           then
             (case set_header x_v_l packet_in_bl of
              | SOME header =>
               (case assign' scope_list header (lval_varname (varn_name ^(get_id "headerLvalue"))) of
                | SOME scope_list' =>
                 SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP sz packet_in_bl))):(core_v_ext, 'b) sum), scope_list', status_returnv v_bot)
                | NONE => NONE)
              | NONE => NONE)
           else
            (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
            SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet [])):(core_v_ext, 'b) sum)) ^(get_id "parseError") (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans ^(get_id "reject"))
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition packet_in_lookahead_gen_def:
 (packet_in_lookahead_gen ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "targ1"))) of
    | SOME dummy_v =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits dummy_v of
        | SOME sz =>
          if sz <= LENGTH packet_in_bl
          then
             (case set_v dummy_v packet_in_bl of
              | SOME v =>
               SOME (ascope, scope_list, status_returnv v)
              | NONE => NONE)
          else
           (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
           SOME (ascope_update_v_map ascope ^(get_id "parseError") (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans ^(get_id "reject"))
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition lookup_lval_bit32_def:
 (lookup_lval_bit32 ss bit32_lval =
  case lookup_lval' ss bit32_lval of
   | SOME (v_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End
Definition packet_in_advance_gen_def:
 (packet_in_advance_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_bit32 scope_list (lval_varname (varn_name ^(get_id "bits"))) of
    | SOME n_bits =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
        if n_bits <= LENGTH packet_in_bl
        then
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP n_bits packet_in_bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        else
         (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
         SOME (ascope_update_v_map ascope ^(get_id "parseError") (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans ^(get_id "reject"))
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

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
Definition packet_out_emit_gen_def:
 (packet_out_emit_gen (ascope_lookup:'a -> num -> (core_v_ext + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_ext_ref i) =>
   (case lookup_ascope_gen ascope_lookup ascope i of
    | SOME (INL (core_v_ext_packet packet_out_bl)) =>
     (case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "data"))) of
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


(** Implementations **)

Definition header_is_valid_def:
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status_returnv (v_bool valid_bit))
  | _ => NONE
 )
End


Definition header_set_valid_def:
 (header_set_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign' scope_list (v_header T x_v_l) (lval_varname (varn_name ^(get_id "this"))) of
    | SOME scope_list' =>
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid_def:
 (header_set_invalid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name ^(get_id "this"))) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign' scope_list (v_header F x_v_l) (lval_varname (varn_name ^(get_id "this"))) of
    | SOME scope_list' =>             
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End
*)
val _ = export_theory ();
