Theory p4_ebpf
Ancestors
  p4 p4_aux p4_core

(* TODO: Put all the stuff that's shared between this and VSS in coreTheory *)

(* TODO: Make actual representations of these extern objects *)
Datatype:
 ebpf_v_ext =
   ebpf_v_ext_counterArray (word32 list)
 | ebpf_v_ext_array_table
 | ebpf_v_ext_hash_table
End

Type ebpf_sum_v_ext = “:(core_v_ext, ebpf_v_ext) sum”

Type ebpf_ctrl = “:(string, (((e_list -> bool) # num), string # e_list) alist) alist”

(* The architectural state type of the eBPF architecture model *)
Type ebpf_ascope = “:(num # ((num, ebpf_sum_v_ext) alist) # ((string, v) alist) # ebpf_ctrl # num)”

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition ebpf_ascope_lookup_def:
 ebpf_ascope_lookup = ascope_lookup_gen:ebpf_ascope -> num -> ebpf_sum_v_ext option
End

Definition ebpf_ascope_update_def:
 ebpf_ascope_update = ascope_update_gen:ebpf_ascope -> num -> ebpf_sum_v_ext -> ebpf_ascope
End

Definition ebpf_ascope_update_v_map_def:
 ebpf_ascope_update_v_map = ascope_update_v_map_gen:ebpf_ascope -> string -> v -> ebpf_ascope
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

(************************)
(* CounterArray methods *)
(************************)

(*************)
(* construct *)

(* Note that the "sparse" flag of the constructor is irrelevant for our representation, so this isn't used here. *)
Definition CounterArray_construct:
 (CounterArray_construct ((counter, ext_obj_map, v_map, ctrl, oracle_index):ebpf_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "max_index")) of
  | SOME (v_bit (bl,n)) =>
   let bitstring_list = REPLICATE (v2n bl) ((n2w 0):word32) in
   let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (ebpf_v_ext_counterArray bitstring_list)) in
   (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME ((counter + 1, ext_obj_map', v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

(*************)
(* increment *)

(* Note that this always succeeds: if index is out of range, nothing will be updated *)
Definition update_index_def:
 (update_index _ _ [] = []) /\
 (update_index upd 0 (h::t) = ((upd h)::t)) /\
 (update_index upd (SUC n) (h::t) = (h::(update_index upd n t)))
End

Definition CounterArray_increment:
 (CounterArray_increment ((counter, ext_obj_map, v_map, ctrl, oracle_index):ebpf_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (ebpf_v_ext_counterArray bitstring_list)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "index")) of
      | SOME (v_bit (bl,n)) =>
       let bitstring_list' = update_index ($word_add (1w:word32)) (v2n bl) bitstring_list in
        SOME ((counter, AUPDATE ext_obj_map (i, INR (ebpf_v_ext_counterArray bitstring_list')), v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(*******)
(* add *)

Definition CounterArray_add:
 (CounterArray_add ((counter, ext_obj_map, v_map, ctrl, oracle_index):ebpf_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (ebpf_v_ext_counterArray bitstring_list)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "index")) of
      | SOME (v_bit (bl,n)) =>
       (case lookup_lval scope_list (lval_varname (varn_name "value")) of
        | SOME (v_bit (bl',n')) =>
         let bitstring_list' = update_index ($word_add ((v2w bl'):word32)) (v2n bl) bitstring_list in
          SOME ((counter, AUPDATE ext_obj_map (i, INR (ebpf_v_ext_counterArray bitstring_list')), v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
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
Definition ebpf_input_f_def:
 (ebpf_input_f n (io_list:in_out_list, ascope:ebpf_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   let (counter, ext_obj_map, v_map, ctrl, oracle_index) = reset_ext_obj_map_gen n ascope in
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
       SOME (t, (counter, ext_obj_map'', v_map'', ctrl, oracle_index):ebpf_ascope)
      | _ => NONE)
    | _ => NONE))
End

Definition ebpf_copyin_pbl_def:
 ebpf_copyin_pbl = copyin_pbl_gen:ebpf_ascope copyin_pbl
End

Definition ebpf_copyout_pbl_def:
 ebpf_copyout_pbl = copyout_pbl_gen:ebpf_ascope copyout_pbl
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
(* This will also look up the value of "accept" and only output a packet if it is true *)
Definition ebpf_output_f_def:
 ebpf_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl, oracle_index):ebpf_ascope) =
  case ALOOKUP v_map "accept" of
  | SOME (v_bool T) =>
   (case lookup_obj ext_obj_map v_map "packet_copy" of
    | SOME (INL (core_v_ext_packet bl)) =>
     (case ALOOKUP v_map "inCtrl" of
      | SOME (v_struct fields) =>
       (case ebpf_inputPort_to_num fields of
        | SOME port =>
         SOME (in_out_list++[(bl, port)], (counter, ext_obj_map, v_map, ctrl, oracle_index))
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | SOME (v_bool F) => SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl, oracle_index))
  | _ => NONE
End

(* Longest prefix wins in tables with only lpm and exact keys, otherwise smallest priority *)
Definition ebpf_apply_table_f_def:
 ebpf_apply_table_f = apply_table_f_gen (\mk_list. MEM mk_lpm mk_list /\ EVERY (\mk. mk = mk_exact \/ mk = mk_lpm) mk_list):ebpf_ascope apply_table_f
End

Definition ebpf_get_oracle_index_def:
 ebpf_get_oracle_index = get_oracle_index_gen:ebpf_ascope get_oracle_index
End

Definition ebpf_set_oracle_index_def:
 ebpf_set_oracle_index = set_oracle_index_gen:ebpf_ascope set_oracle_index
End
