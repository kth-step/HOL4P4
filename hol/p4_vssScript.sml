Theory p4_vss
Ancestors
  p4 p4_aux p4_core

Datatype:
 vss_v_ext =
   vss_v_ext_ipv4_checksum (word16 list)
End
Type vss_sum_v_ext = “:(core_v_ext, vss_v_ext) sum”

Type vss_ctrl = “:(string, (((e_list -> bool) # num), string # e_list) alist) alist”

(* The architectural state type of the VSS architecture model *)
Type vss_ascope = “:(num # ((num, vss_sum_v_ext) alist) # ((string, v) alist) # vss_ctrl # num)”

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition vss_ascope_lookup_def:
 vss_ascope_lookup = ascope_lookup_gen:vss_ascope -> num -> vss_sum_v_ext option
End

Definition vss_ascope_update_def:
 vss_ascope_update = ascope_update_gen:vss_ascope -> num -> vss_sum_v_ext -> vss_ascope
End

Definition vss_ascope_update_v_map_def:
 vss_ascope_update_v_map = ascope_update_v_map_gen:vss_ascope -> string -> v -> vss_ascope
End

Definition vss_packet_in_extract:
 vss_packet_in_extract = packet_in_extract_gen vss_ascope_lookup vss_ascope_update vss_ascope_update_v_map
End

Definition vss_packet_in_lookahead:
 vss_packet_in_lookahead = packet_in_lookahead_gen vss_ascope_lookup vss_ascope_update_v_map
End

Definition vss_packet_in_advance:
 vss_packet_in_advance = packet_in_advance_gen F vss_ascope_lookup vss_ascope_update vss_ascope_update_v_map
End

Definition vss_packet_out_emit:
 vss_packet_out_emit = packet_out_emit_gen vss_ascope_lookup vss_ascope_update
End

Definition vss_verify:
 (vss_verify (ascope:vss_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen vss_ascope_update_v_map (ascope, g_scope_list, scope_list))
End


(**********************************************************)
(*                     EXTERN OBJECTS                     *)
(**********************************************************)

(**********************)
(* Checksum16 methods *)
(**********************)

(*************)
(* construct *)

Definition Checksum16_construct:
 (Checksum16_construct ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (vss_v_ext_ipv4_checksum ([]:word16 list))) in
  (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_obj_map', v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
   | NONE => NONE)
 )
End


(*********)
(* clear *)

Definition Checksum16_clear:
 (Checksum16_clear ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum ([]:word16 list))), v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
  | _ => NONE
 )
End


(**********)
(* update *)

(* Note that this assumes the order of fields in the header is correct *)
Definition Checksum16_update:
 (Checksum16_update ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum (ipv4_checksum ++ checksum_incr))), v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(**********)
(* remove *)

(* Adds the ones' complement of each word: x - y = x + ~y in ones' complement *)
Definition Checksum16_remove:
 (Checksum16_remove ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum (ipv4_checksum ++ MAP word_1comp checksum_incr))), v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(*******)
(* get *)

Definition Checksum16_get:
 (Checksum16_get ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope, scope_list, status_returnv (v_bit (w16 (compute_checksum16 ipv4_checksum))))
    | _ => NONE)
  | _ => NONE
 )
End


(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
(* Frames start at the data link layer and exclude the Ethernet CRC, which the arbiter
 * checks and removes and the demux adds (spec 5.2.1, 5.2.3). The parser gets the whole frame,
 * and the original frame is kept for the CPU port *)
(* TODO: Note that this also resets parseError to 0 *)
Definition vss_input_f_def:
  (vss_input_f n (io_list:in_out_list, ascope:vss_ascope) =
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let (counter, ext_obj_map, v_map, ctrl, oracle_index) = reset_ext_obj_map_gen n ascope in
    (case (ALOOKUP v_map "b_in", ALOOKUP v_map "b_out", ALOOKUP v_map "payload", ALOOKUP v_map "b_orig") of
     | (SOME (v_ext_ref i), SOME (v_ext_ref i'), SOME (v_ext_ref i''), SOME (v_ext_ref i''')) =>
      let ext_obj_map' = AUPDATE_LIST ext_obj_map [(i, INL (core_v_ext_packet bl));
                                                   (i', INL (core_v_ext_packet []));
                                                   (i'', INL (core_v_ext_packet []));
                                                   (i''', INL (core_v_ext_packet bl))] in
      let v_map' = AUPDATE_LIST v_map [("inCtrl", v_struct [("inputPort", v_bit (w4 (n2w p)))]);
                                       ("parseError", v_bit (fixwidth 32 (n2v 0), 32))] in
       SOME (t, (counter, ext_obj_map', v_map', ctrl, oracle_index):vss_ascope)
     | _ => NONE))
End

Definition vss_copyin_pbl_def:
 vss_copyin_pbl = copyin_pbl_gen:vss_ascope copyin_pbl
End

Definition vss_copyout_pbl_def:
 vss_copyout_pbl = copyout_pbl_gen:vss_ascope copyout_pbl
End

(* Hands the headers to the pipe and the unparsed rest of the frame to the demux *)
Definition vss_parser_runtime_def:
 vss_parser_runtime (i, io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope) =
  (case (ALOOKUP v_map "parsedHeaders", ALOOKUP v_map "b_in", ALOOKUP v_map "payload") of
   | (SOME (v_struct hdrs), SOME (v_ext_ref j), SOME (v_ext_ref j')) =>
    (case ALOOKUP ext_obj_map j of
     | SOME (INL (core_v_ext_packet bl)) =>
      let ext_obj_map' = AUPDATE_LIST ext_obj_map [(j, INL (core_v_ext_packet [])); (j', INL (core_v_ext_packet bl))] in
       SOME (i+1, io_list, io_list', (counter, ext_obj_map', AUPDATE v_map ("headers", v_struct hdrs), ctrl, oracle_index))
     | _ => NONE)
   | _ => NONE)
End

Definition vss_pre_deparser_def:
 vss_pre_deparser (i, io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope) =
  (case ALOOKUP v_map "headers" of
   | SOME (v_struct hdrs) =>
    let v_map' = AUPDATE v_map ("outputHeaders", v_struct hdrs) in
     SOME (i+1, io_list, io_list', (counter, ext_obj_map, v_map', ctrl, oracle_index))
   | _ => NONE)
End

(* The demux sends a packet for the recirculation port 13 back to the input, arriving on port 13 *)
Definition vss_demux_def:
 vss_demux (i, io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope) =
  (case ALOOKUP v_map "outCtrl" of
   | SOME (v_struct [(fldname, v_bit (bl, n))]) =>
    if v2n bl = 13
    then
     (case (lookup_obj ext_obj_map v_map "b_out", lookup_obj ext_obj_map v_map "payload") of
      | (SOME (INL (core_v_ext_packet headers)), SOME (INL (core_v_ext_packet payload))) =>
       SOME (0, (headers++payload, 13)::io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index))
      | _ => NONE)
    else SOME (i+1, io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index))
   | _ => NONE)
End

(* Ports 0-7 get the deparsed headers and the payload, the CPU port 14 the original frame;
 * the drop port 15 and the illegal ports 8-12 drop the packet (spec 5.2.3) *)
Definition vss_demux_out_def:
 vss_demux_out port headers payload frame =
  if port < 8 then [(headers++payload, port)]
  else if port = 14 then [(frame, port)]
  else []
End

(* NOTE: "b" renamed to "b_out" *)
Definition vss_output_f_def:
 vss_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl, oracle_index):vss_ascope) =
  (case (lookup_obj ext_obj_map v_map "b_out", lookup_obj ext_obj_map v_map "payload", lookup_obj ext_obj_map v_map "b_orig") of
   | (SOME (INL (core_v_ext_packet headers)), SOME (INL (core_v_ext_packet payload)), SOME (INL (core_v_ext_packet frame))) =>
    (case ALOOKUP v_map "outCtrl" of
     | SOME (v_struct [(fldname, v_bit (bl, n))]) =>
      SOME (in_out_list++(vss_demux_out (v2n bl) headers payload frame), (counter, ext_obj_map, v_map, ctrl, oracle_index))
     | _ => NONE)
   | _ => NONE)
End

(* Longest prefix wins in tables with only lpm and exact keys, otherwise smallest priority *)
Definition vss_apply_table_f_def:
 vss_apply_table_f = apply_table_f_gen (\mk_list. MEM mk_lpm mk_list /\ EVERY (\mk. mk = mk_exact \/ mk = mk_lpm) mk_list):vss_ascope apply_table_f
End

Definition vss_get_oracle_index_def:
 vss_get_oracle_index = get_oracle_index_gen:vss_ascope get_oracle_index
End

Definition vss_set_oracle_index_def:
 vss_set_oracle_index = set_oracle_index_gen:vss_ascope set_oracle_index
End
