open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_arch_ebpf";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_cake_auxTheory p4_cake_auxLib p4_cake_exec_semTheory p4_cake_archTheory;
open p4_coreTheory p4_ebpfTheory;

(* Note that the below have been manually translated using the dictionary mapping strings to words64
 * created using p4_transform_cakeLib *)

val _ = type_abbrev("ebpf_sum_v_ext'", “:(core_v_ext', ebpf_v_ext) sum”);

val _ = type_abbrev("ebpf_ctrl'", “:(identifier, tbl') alist”);

(* The architectural state type of the eBPF architecture model *)
val _ = type_abbrev("ebpf_ascope'", “:(num # ((num, ebpf_sum_v_ext') alist) # ((identifier, v') alist) # ebpf_ctrl')”);

Definition ebpf_ascope_lookup'_def:
 ebpf_ascope_lookup' (ascope:ebpf_ascope') ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition ebpf_ascope_update'_def:
 ebpf_ascope_update' ((counter, ext_obj_map, v_map, ctrl):ebpf_ascope') ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition ebpf_ascope_update_v_map'_def:
 ebpf_ascope_update_v_map' ((counter, ext_obj_map, v_map, ctrl):ebpf_ascope') str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition ebpf_packet_in_extract'_def:
 ebpf_packet_in_extract' = packet_in_extract_gen' ebpf_ascope_lookup' ebpf_ascope_update' ebpf_ascope_update_v_map'
End

Definition ebpf_packet_in_lookahead'_def:
 ebpf_packet_in_lookahead' = packet_in_lookahead_gen' ebpf_ascope_lookup' ebpf_ascope_update_v_map'
End

Definition ebpf_packet_in_advance'_def:
 ebpf_packet_in_advance' = packet_in_advance_gen' ebpf_ascope_lookup' ebpf_ascope_update' ebpf_ascope_update_v_map'
End

Definition ebpf_packet_out_emit'_def:
 ebpf_packet_out_emit' = packet_out_emit_gen' ebpf_ascope_lookup' ebpf_ascope_update'
End

Definition ebpf_verify'_def:
 (ebpf_verify' (ascope:ebpf_ascope', g_scope_list, scope_list) =
  verify_gen' ebpf_ascope_update_v_map' (ascope, g_scope_list, scope_list))
End

(**********************************************************)
(*                     EXTERN OBJECTS                     *)
(**********************************************************)

(************************)
(* CounterArray methods *)
(************************)

(*************)
(* construct *)

(* Note that the "sparse" flag of the constructor is irrelevant for our representation, so this isn't used here. *)
Definition CounterArray_construct'_def:
 (CounterArray_construct' (ebpf_ascope, g_scope_list:g_scope_list', scope_list) =
 SOME (ebpf_ascope, scope_list, status'_returnv v'_bot)
(*
  case lookup_lval'' scope_list (lval'_varname (varn'_name 75w)) of
  | SOME (v'_bit (bl,n)) =>
   let bitstring_list = REPLICATE (v2n bl) ((n2w 0):word32) in
   let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (ebpf_v_ext_counterArray bitstring_list)) in
   (case assign' scope_list (v'_ext_ref counter) (lval'_varname (varn'_name 3w)) of
    | SOME scope_list' =>
     SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status'_returnv v'_bot)
    | NONE => NONE)
  | _ => NONE
*)
 )
End

(*************)
(* increment *)
(* TODO: Dummy *)
(* Note that this always succeeds: if index is out of range, nothing will be updated *)
Definition update_index_def:
 (update_index _ _ [] = []) /\
 (update_index upd 0 (h::t) = ((upd h)::t)) /\
 (update_index upd (SUC n) (h::t) = (h::(update_index upd n t)))
End
(* TODO: Dummy *)
Definition CounterArray_increment'_def:
 (CounterArray_increment' (ebpf_ascope, g_scope_list:g_scope_list', scope_list) =
 SOME (ebpf_ascope, scope_list, status'_returnv v'_bot)
(*
  case lookup_lval'' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (ebpf_v_ext_counterArray bitstring_list)) =>
     (case lookup_lval'' scope_list (lval'_varname (varn'_name 19w)) of
      | SOME (v'_bit (bl,n)) =>
       let bitstring_list' = update_index ($word_add (1w:word32)) (v2n bl) bitstring_list in
        SOME ((counter, AUPDATE ext_obj_map (i, INR (ebpf_v_ext_counterArray bitstring_list')), v_map, ctrl), scope_list, status'_returnv v'_bot)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
*)
 )
End

(*******)
(* add *)
(* TODO: Dummy *)
Definition CounterArray_add'_def:
 (CounterArray_add' (ebpf_ascope, g_scope_list:g_scope_list', scope_list) =
 SOME (ebpf_ascope, scope_list, status'_returnv v'_bot)
(*
  case lookup_lval'' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (ebpf_v_ext_counterArray bitstring_list)) =>
     (case lookup_lval'' scope_list (lval'_varname (varn'_name 19w)) of
      | SOME (v'_bit (bl,n)) =>
       (case lookup_lval'' scope_list (lval'_varname (varn'_name 20w)) of
        | SOME (v'_bit (bl',n')) =>
         let bitstring_list' = update_index ($word_add ((v2w bl'):word32)) (v2n bl) bitstring_list in
          SOME ((counter, AUPDATE ext_obj_map (i, INR (ebpf_v_ext_counterArray bitstring_list')), v_map, ctrl), scope_list, status'_returnv v'_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
*)
 )
End

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
Definition ebpf_input_f'_def:
 (ebpf_input_f' tau_uninit_v (io_list:in_out_list', (counter, ext_obj_map, v_map, ctrl):ebpf_ascope') =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Implement persistence between packets when you fully model persistent extern objects *)
   let ext_obj_map' = AUPDATE_LIST [] [(0, INL (core_v_ext'_packet bl));
                                       (1, INL (core_v_ext'_packet bl))] in
   let counter' = 2 in
   (* TODO: Garbage collection? *)
   let v_map' = AUPDATE_LIST v_map [(^(get_id "packet"), v'_ext_ref 0);
                                    (^(get_id "packet_copy"), v'_ext_ref 1);
                                    (^(get_id "headers"), tau_uninit_v);
                                    (^(get_id "accept"), v'_bit ([F], 1));
                                    (^(get_id "inCtrl"), v'_struct [(^(get_id "inputPort"),v'_bit ((fixwidth 4 $ n2v p, 4)))]);
                                    (^(get_id "parseError"), v'_bit (fixwidth 32 (n2v 0), 32));
] in
     SOME (t, (counter', ext_obj_map', v_map', ctrl):ebpf_ascope')
    | _ => NONE)
End
(*
Definition ebpf_input_f_def:
 (ebpf_input_f tau_uninit_v (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet bl))] in
   (* TODO: Slightly vestigial from the VSS model:
    * needed to remember port when packet is accepted. Change to a more elegant solution later *)
   let v_map' = AUPDATE_LIST v_map [("packet", v_ext_ref counter);
                                    ("packet_copy", v_ext_ref counter+1);
                                    ("headers", tau_uninit_v);
                                    ("accept", v_bit ([F], 1));
                                    ("inCtrl", v_struct [("inputPort",v_bit (w4 (n2w p)))]);
                                    ("parseError", v_bit (fixwidth 32 (n2v 0), 32))] in
    SOME (t, (counter, ext_obj_map', v_map', ctrl):ebpf_ascope)
    | _ => NONE)
End
*)

Definition ebpf_reduce_nonout'_def:
 (ebpf_reduce_nonout' ([], elist, v_map) = SOME []) /\
 (ebpf_reduce_nonout' (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, ebpf_reduce_nonout' (dlist, elist, v_map))
  else
   (case e of
    | (e'_var (varn'_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e'_v v, ebpf_reduce_nonout' (dlist, elist, v_map))
       else oCONS (e'_v (init_out_v_cake v), ebpf_reduce_nonout' (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (ebpf_reduce_nonout' (_, _, v_map) = NONE)
End

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
Definition ebpf_copyin_pbl'_def:
 ebpf_copyin_pbl' (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope') =
  case ebpf_reduce_nonout' (dlist, elist, v_map) of
  | SOME elist' =>
   copyin' xlist dlist elist' [v_map_to_scope' v_map] [ [] ]
  | NONE => NONE
End

(* TODO: Does anything need to be looked up for this function? *)
(* Note that this re-uses the copyout function intended for P4 functions *)
Definition ebpf_copyout_pbl'_def:
 ebpf_copyout_pbl' (g_scope_list, (counter, ext_obj_map, v_map, ctrl):ebpf_ascope', dlist, xlist, (status:status')) =
  case copyout_pbl_gen' xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap' v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):ebpf_ascope')
    | NONE => NONE)
  | _ => NONE
End

Definition ebpf_lookup_obj'_def:
 ebpf_lookup_obj' ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v'_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

Definition ebpf_inputPort_to_num'_def:
 ebpf_inputPort_to_num' fields =
  case fields of
  | [(key, value)] =>
   (case value of
    | v'_bit bitv =>
     SOME (v2n $ FST bitv)
    | _ => NONE)
  | _ => NONE
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* This will also look up the value of "pass" and only output a packet if it is true *)
Definition ebpf_output_f'_def:
 ebpf_output_f' (in_out_list:in_out_list', (counter, ext_obj_map, v_map, ctrl):ebpf_ascope') =
  case ALOOKUP v_map ^(get_id "accept") of
  | SOME (v'_bool T) =>
   (case ebpf_lookup_obj' ext_obj_map v_map ^(get_id "packet_copy") of
    | SOME (INL (core_v_ext'_packet bl)) =>
     (case ALOOKUP v_map ^(get_id "inCtrl") of
      | SOME (v'_struct fields) =>
       (case ebpf_inputPort_to_num' fields of
        | SOME port =>
         SOME (in_out_list++[(bl, port)], (counter, ext_obj_map, v_map, ctrl))
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | SOME (v'_bool F) => SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
  | _ => NONE
End

val ebpf_apply_table_f'_def =
 if matching_optimization
 then Define ‘ebpf_apply_table_f' = T’
 else
  Define
 ‘ebpf_apply_table_f' (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):ebpf_ascope') =
  (* TODO: Note that this function could do other stuff here depending on table name.
   *       Ideally, one could make a general, not hard-coded, solution for this *)
  case ALOOKUP ctrl x of
   | SOME table =>
    (case vl_of_el' e_l of
     | SOME v_l =>
      (case table of
         tbl'_impl f => SOME $ f $ v_l
       | tbl'_regular tbl =>
        (* Largest priority wins *)
        SOME (FST $ FOLDL_MATCH' v_l ((x', e_l'), NONE) tbl))
     | NONE => NONE)
   | NONE => NONE’
;

val ebpf_apply_table_f''_def =
 if matching_optimization
 then Define
 ‘ebpf_apply_table_f'' (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):ebpf_ascope') =
  (* TODO: Note that this function could do other stuff here depending on table name.
   *       Ideally, one could make a general, not hard-coded, solution for this *)
  case ALOOKUP ctrl x of
   | SOME table =>
    (case e_list_to_word64s_list e_l of
     | SOME w_l =>
      (case table of
         tbl'_impl f => SOME $ f $ w_l
       | tbl'_regular tbl =>
        (* TODO: Largest priority wins (like for P4Runtime) is hard-coded *)
        SOME (FST $ FOLDL_MATCH'' w_l ((x', e_l'), NONE) tbl))
     | NONE => NONE)
   | NONE => NONE’
 else Define ‘ebpf_apply_table_f'' = T’
;

val _ = export_theory ();
