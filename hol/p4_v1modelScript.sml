open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory p4_coreTheory;

val _ = new_theory "p4_v1model";

(* TODO: v1model uses a checksum in the verify_checksum and update_checksum externs *)
Datatype:
 v1model_v_ext =
   v1model_v_ext_ipv4_checksum (word16 list)
 | v1model_v_ext_counter
 | v1model_v_ext_direct_counter
 | v1model_v_ext_meter
 | v1model_v_ext_direct_meter
 | v1model_v_ext_register
End
val _ = type_abbrev("v1model_sum_v_ext", ``:(core_v_ext, v1model_v_ext) sum``);

val _ = type_abbrev("v1model_ctrl", ``:(string, (e_list, string # e_list) alist) alist``);

(* The architectural state type of the V1Model architecture model *)
val _ = type_abbrev("v1model_ascope", ``:(num # ((num, v1model_sum_v_ext) alist) # ((string, v) alist) # v1model_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition v1model_ascope_lookup_def:
 v1model_ascope_lookup (ascope:v1model_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition v1model_ascope_update_def:
 v1model_ascope_update ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition v1model_packet_in_extract:
 v1model_packet_in_extract = packet_in_extract_gen v1model_ascope_lookup v1model_ascope_update
End

Definition v1model_packet_out_emit:
 v1model_packet_out_emit = packet_out_emit_gen v1model_ascope_lookup v1model_ascope_update
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* NOTE: 511 is the default drop port *)
Definition v1model_mark_to_drop_def:
 v1model_mark_to_drop (v1model_ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list, status:status) =
  case assign scope_list (v_bit (fixwidth 9 (n2v 511), 9)) (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") of
   | SOME scope_list' =>
    SOME (v1model_ascope, g_scope_list, scope_list', status_returnv v_bot)
   | NONE => NONE
End

(**********************)
(* Checksum methods   *)
(**********************)

(*************************)
(* TODO: verify_checksum *)

(*************************)
(* TODO: update_checksum *)

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition v1model_input_f_def:
 (v1model_input_f (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (case ALOOKUP v_map "b" of
    | SOME (v_ext_ref i) =>
     let ext_obj_map' = AUPDATE ext_obj_map (i, INL (core_v_ext_packet bl)) in
     (case ALOOKUP v_map "standard_metadata" of
      | SOME (v_struct struct) =>
       let v_map' = AUPDATE v_map ("standard_metadata", v_struct (AUPDATE struct ("ingress_port", v_bit (w9 (n2w p))))) in
       SOME (t, (counter, ext_obj_map', v_map', ctrl):v1model_ascope)
      | _ => NONE)
    | _ => NONE))
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition v1model_reduce_nonout_def:
 (v1model_reduce_nonout ([], elist, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, v1model_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v v), v1model_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout (_, _, v_map) = NONE)
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
(* TODO: Remove these and keep "v_map" as just a regular scope? *)
Definition v_map_to_scope_def:
 (v_map_to_scope [] = []) /\
 (v_map_to_scope (((k, v)::t):(string, v) alist) =
  ((varn_name k, (v, NONE:lval option))::v_map_to_scope t)
 )
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition scope_to_vmap_def:
 (scope_to_vmap [] = SOME []) /\
 (scope_to_vmap ((vn, (v:v, lval_opt:lval option))::t) =
  case vn of
   | (varn_name k) => oCONS ((k, v), scope_to_vmap t)
   | _ => NONE
 )
End

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
(* TODO: Don't reduce all arguments at once? *)
Definition v1model_copyin_pbl_def:
 v1model_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope, pbl_type) =
  case v1model_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (* Note: no initialisation of parser error here *)
   copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ]
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition v1model_copyout_pbl_def:
 v1model_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope, dlist, xlist, pbl_type, (status:status)) =
  case copyout xlist dlist [ [] ; [] ] [v_map_to_scope v_map] g_scope_list of
  | SOME (_, [v_map_scope]) =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):v1model_ascope)
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Make generic *)
Definition v1model_lookup_obj_def:
 v1model_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* Simply transfers the value of parsedHdr to hdr *)
Definition v1model_postparser_def:
 v1model_postparser ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case ALOOKUP v_map "parsedHdr" of
   | SOME v =>
    let v_map' = AUPDATE v_map ("hdr", v) in
     SOME (counter, ext_obj_map, v_map', ctrl)
   | _ => NONE)
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
Definition v1model_output_f_def:
 v1model_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case v1model_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case ALOOKUP v_map "standard_metadata" of
     | SOME (v_struct struct) =>
      (case ALOOKUP struct "egress_spec" of
       | SOME (v_bit (port_bl, n)) =>
        let port_out = v2n port_bl in
         if port_out = 511
         then SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
         else SOME (in_out_list++[(bl, port_out)], (counter, ext_obj_map, v_map, ctrl))
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

Definition v1model_apply_table_f_def:
 v1model_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (* TODO: Note that this function could do other stuff here depending on table name.
   *       Ideally, one could make a general, not hard-coded, solution for this *)
  (case ALOOKUP ctrl x of
   | SOME table =>
    (* TODO: This now implicitly uses only exact matching against stored tables.
     * Ideally, this should be able to use lpm and other matching kinds *)
    (case ALOOKUP table e_l of
     | SOME (x'', e_l'') => SOME (x'', e_l'')
     | NONE => SOME (x', e_l'))
   | NONE => NONE)
End

val _ = export_theory ();
