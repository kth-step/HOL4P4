open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory p4_coreTheory;

val _ = new_theory "p4_ebpf";

(* TODO: Put all the stuff that's shared between this and VSS in coreTheory *)

(* TODO: Make actual representations of these extern objects *)
Datatype:
 ebpf_v_ext =
   ebpf_v_ext_counterArray
 | ebpf_v_ext_array_table
 | ebpf_v_ext_hash_table
End

val _ = type_abbrev("ebpf_sum_v_ext", ``:(core_v_ext, ebpf_v_ext) sum``);

val _ = type_abbrev("ebpf_ctrl", ``:(string, (e_list, string # e_list) alist) alist``);

(* The architectural state type of the eBPF architecture model *)
val _ = type_abbrev("ebpf_ascope", ``:(num # ((num, ebpf_sum_v_ext) alist) # ((string, v) alist) # ebpf_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition ebpf_ascope_lookup_def:
 ebpf_ascope_lookup (ascope:ebpf_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition ebpf_ascope_update_def:
 ebpf_ascope_update ((counter, ext_obj_map, v_map, ctrl):ebpf_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition ebpf_ascope_update_v_map_def:
 ebpf_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):ebpf_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition ebpf_packet_in_extract:
 ebpf_packet_in_extract = packet_in_extract_gen ebpf_ascope_lookup ebpf_ascope_update ebpf_ascope_update_v_map
End

Definition ebpf_packet_in_lookahead:
 ebpf_packet_in_lookahead = packet_in_lookahead_gen ebpf_ascope_lookup ebpf_ascope_update_v_map
End

Definition ebpf_packet_in_advance:
 ebpf_packet_in_advance = packet_in_advance_gen ebpf_ascope_lookup ebpf_ascope_update ebpf_ascope_update_v_map
End

Definition ebpf_packet_out_emit:
 ebpf_packet_out_emit = packet_out_emit_gen ebpf_ascope_lookup ebpf_ascope_update
End

Definition ebpf_verify:
 (ebpf_verify (ascope:ebpf_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen ebpf_ascope_update_v_map (ascope, g_scope_list, scope_list))
End
    
(**********************************************************)
(*                     EXTERN OBJECTS                     *)
(**********************************************************)

(* TODO: Models of all the extern objects in eBPF *)

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)

(* The first 14 bytes are always the Eth-II header.
 * The last 4 bytes are always the CRC checksum.
 * In between these is the IPv4 payload. The first 16 bytes
 * of this are mandatory fields. Depending on the IHL header
 * field, 0-46 bytes of option field follows. *)
(* NOTE: "b" renamed to "b_in" *)
(* TODO: Note that this also resets parseError to 0 *)
Definition ebpf_input_f_def:
 (ebpf_input_f (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (case ALOOKUP v_map "packet" of
    | SOME (v_ext_ref i) =>
     let ext_obj_map' = AUPDATE ext_obj_map (i, INL (core_v_ext_packet bl)) in
     (* TODO: Below is a bit of a hack. We should replace all "AUPDATE" with an assign
      * function for ebpf_ascope. *)
     (* TODO: Slightly vestigial from the VSS model:
      * needed to remember port when packet is accepted. Change to a more elegant solution later *)
     let v_map' = AUPDATE v_map ("inCtrl", v_struct [("inputPort",v_bit (w4 (n2w p)))]) in
     let v_map'' = AUPDATE v_map' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
     (case ALOOKUP v_map'' "packet_copy" of
      | SOME (v_ext_ref i') =>
       let ext_obj_map'' = AUPDATE ext_obj_map' (i', INL (core_v_ext_packet bl)) in
       SOME (t, (counter, ext_obj_map'', v_map'', ctrl):ebpf_ascope)
      | _ => NONE)
    | _ => NONE))
End

Definition ebpf_reduce_nonout_def:
 (ebpf_reduce_nonout ([], elist, v_map) = SOME []) /\
 (ebpf_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, ebpf_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, ebpf_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v v), ebpf_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (ebpf_reduce_nonout (_, _, v_map) = NONE)
End

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

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
(* TODO: Don't reduce all arguments at once? *)
Definition ebpf_copyin_pbl_def:
 ebpf_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope) =
  case ebpf_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ]
  | NONE => NONE
End

(* TODO: Does anything need to be looked up for this function? *)
(* Note that this re-uses the copyout function intended for P4 functions *)
Definition ebpf_copyout_pbl_def:
 ebpf_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):ebpf_ascope)
    | NONE => NONE)
  | _ => NONE
End

Definition ebpf_lookup_obj_def:
 ebpf_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

Definition ebpf_inputPort_to_num_def:
 ebpf_inputPort_to_num fields =
  case fields of
  | [(key, value)] =>
   (case value of
    | v_bit bitv =>
     SOME (v2n $ FST bitv)
    | _ => NONE)
  | _ => NONE
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* This will also look up the value of "pass" and only output a packet if it is true *)
Definition ebpf_output_f_def:
 ebpf_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope) =
  case ALOOKUP v_map "accept" of
  | SOME (v_bool T) =>
   (case ebpf_lookup_obj ext_obj_map v_map "packet_copy" of
    | SOME (INL (core_v_ext_packet bl)) =>
     (case ALOOKUP v_map "inCtrl" of
      | SOME (v_struct fields) =>
       (case ebpf_inputPort_to_num fields of
        | SOME port =>
         SOME (in_out_list++[(bl, port)], (counter, ext_obj_map, v_map, ctrl))
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | SOME (v_bool F) => SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
  | NONE => NONE
End

Definition ebpf_apply_table_f_def:
 ebpf_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):ebpf_ascope) =
  (* TODO: Note that this function could do other stuff here depending on table name.
   *       Ideally, one could make a general, not hard-coded, solution for this *)
  case ALOOKUP ctrl x of
   | SOME table =>
    (* TODO: This now implicitly uses only exact matching against stored tables.
     * Ideally, this should be able to use lpm and other matching kinds *)
    (case ALOOKUP table e_l of
     | SOME (x'', e_l'') => SOME (x'', e_l'')
     | NONE => SOME (x', e_l'))
   | NONE => NONE
End

val _ = export_theory ();
