open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory p4_coreTheory;

val _ = new_theory "p4_vss";

Datatype:
 vss_v_ext =
   vss_v_ext_ipv4_checksum (word16 list)
End
val _ = type_abbrev("vss_sum_v_ext", ``:(core_v_ext, vss_v_ext) sum``);

val _ = type_abbrev("vss_ctrl", ``:(string, (((e_list -> bool) # num), string # e_list) alist) alist``);

(* The architectural state type of the VSS architecture model *)
val _ = type_abbrev("vss_ascope", ``:(num # ((num, vss_sum_v_ext) alist) # ((string, v) alist) # vss_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition vss_ascope_lookup_def:
 vss_ascope_lookup (ascope:vss_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition vss_ascope_update_def:
 vss_ascope_update ((counter, ext_obj_map, v_map, ctrl):vss_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition vss_ascope_update_v_map_def:
 vss_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):vss_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition vss_packet_in_extract:
 vss_packet_in_extract = packet_in_extract_gen vss_ascope_lookup vss_ascope_update vss_ascope_update_v_map
End

Definition vss_packet_in_lookahead:
 vss_packet_in_lookahead = packet_in_lookahead_gen vss_ascope_lookup vss_ascope_update_v_map
End

Definition vss_packet_in_advance:
 vss_packet_in_advance = packet_in_advance_gen vss_ascope_lookup vss_ascope_update vss_ascope_update_v_map
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
 (Checksum16_construct ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (vss_v_ext_ipv4_checksum ([]:word16 list))) in
  (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
   | NONE => NONE)
 )
End


(*********)
(* clear *)

Definition Checksum16_clear:
 (Checksum16_clear ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum ([]:word16 list))), v_map, ctrl), scope_list, status_returnv v_bot)
  | _ => NONE
 )
End


(**********)
(* update *)

(* Note that this assumes the order of fields in the header is correct *)
Definition Checksum16_update:
 (Checksum16_update ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum (ipv4_checksum ++ checksum_incr))), v_map, ctrl), scope_list, status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(*******)
(* get *)

Definition Checksum16_get:
 (Checksum16_get ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     SOME ((counter, ext_obj_map, v_map, ctrl):vss_ascope, scope_list, status_returnv (v_bit (w16 (compute_checksum16 ipv4_checksum))))
    | _ => NONE)
  | _ => NONE
 )
End


(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

Definition get_optional_bits:
 get_optional_bits header = ((v2n (TAKE 4 (DROP 116 header)))*32) - 160
End

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
(* NOTE: VSS example starts out at the data link layer (physical layer ignored):
 * https://en.wikipedia.org/wiki/Ethernet_frame#Frame_%E2%80%93_data_link_layer *)
(* NOTE: VSS example uses only Ethernet II framing:
 * https://en.wikipedia.org/wiki/Ethernet_frame#Ethernet_II *)

(* The first 14 bytes are always the Eth-II header.
 * The last 4 bytes are always the CRC checksum.
 * In between these is the IPv4 payload. The first 16 bytes
 * of this are mandatory fields. Depending on the IHL header
 * field, 0-46 bytes of option field follows. *)
(* NOTE: "b" renamed to "b_in" *)
(* TODO: Note that this also resets parseError to 0 *)
Definition vss_input_f_def:
  (vss_input_f (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let frame_length = LENGTH bl in
    let optional_bits = get_optional_bits bl in
    (case oTAKE (272+optional_bits) bl of
     | SOME header =>
      (case oDROP (272+optional_bits) bl of
       | SOME data_crc =>
        (case ALOOKUP v_map "b_in" of
         | SOME (v_ext_ref i) =>
          let ext_obj_map' = AUPDATE ext_obj_map (i, INL (core_v_ext_packet header)) in
          (case ALOOKUP v_map "data_crc" of
           | SOME (v_ext_ref i') =>
            let ext_obj_map'' = AUPDATE ext_obj_map' (i', INL (core_v_ext_packet data_crc)) in
             (* TODO: Below is a bit of a hack. We should replace all "AUPDATE" with an assign
              * function for vss_ascope. *)
             let v_map' = AUPDATE v_map ("inCtrl", v_struct [("inputPort", v_bit (w4 (n2w p)))]) in
             let v_map'' = AUPDATE v_map' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
              SOME (t, (counter, ext_obj_map'', v_map'', ctrl):vss_ascope)
           | _ => NONE)
         | _ => NONE)
       | NONE => NONE)
     | NONE => NONE)
   | _ => NONE)
End

Definition vss_reduce_nonout_def:
 (vss_reduce_nonout ([], elist, v_map) =
  SOME []
 ) /\
 (vss_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, vss_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, vss_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v v), vss_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (vss_reduce_nonout (_, _, v_map) = NONE)
End

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
(* TODO: Don't reduce all arguments at once? *)
Definition vss_copyin_pbl_def:
 vss_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  case vss_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ]
  | NONE => NONE
End

(* TODO: Does anything need to be looked up for this function? *)
Definition vss_copyout_pbl_def:
 vss_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):vss_ascope)
    | NONE => NONE)
  | _ => NONE
End

Definition vss_parser_runtime_def:
 vss_parser_runtime ((counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  (case ALOOKUP v_map "parsedHeaders" of
   | SOME (v_struct hdrs) =>
    let v_map' = AUPDATE v_map ("headers", v_struct hdrs) in
     SOME (counter, ext_obj_map, v_map', ctrl)
   | _ => NONE)
End

Definition vss_pre_deparser_def:
 vss_pre_deparser ((counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  (case ALOOKUP v_map "headers" of
   | SOME (v_struct hdrs) =>
    let v_map' = AUPDATE v_map ("outputHeaders", v_struct hdrs) in
     SOME (counter, ext_obj_map, v_map', ctrl)
   | _ => NONE)
End

Definition vss_lookup_obj_def:
 vss_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* Add new header + data + Ethernet CRC as a tuple with new output port to output list *)
(* Add data + Ethernet CRC *)
(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
Definition vss_output_f_def:
 vss_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  (case vss_lookup_obj ext_obj_map v_map "b_out" of
   | SOME (INL (core_v_ext_packet headers)) =>
    (case vss_lookup_obj ext_obj_map v_map "data_crc" of
     | SOME (INL (core_v_ext_packet data_crc)) =>
      (case ALOOKUP v_map "outCtrl" of
       | SOME (v_struct [(fldname, v_bit (bl, n))]) =>
        let
         port_out = v2n bl
        in
         if port_out = 15
         then
          SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
         else
          SOME (in_out_list++[(headers++data_crc, port_out)], (counter, ext_obj_map, v_map, ctrl))
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

Definition ctrl_check_ttl:
 (ctrl_check_ttl e_l =
  case e_l of
  | [e] =>
   (case e of
    | e_v v =>
     (case v of
      | (v_bit (bl,n)) =>
       if (v2n bl) > 0
       then SOME ("NoAction", [])
       else SOME ("Send_to_cpu", [])
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition vss_apply_table_f_def:
 vss_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  (* TODO: Note that this function could do other stuff here depending on table name.
   *       Ideally, one could make a general, not hard-coded, solution for this *)
  if x = "check_ttl"
  then
   ctrl_check_ttl e_l
  else
   (case ALOOKUP ctrl x of
    | SOME table =>
     (* TODO: Largest priority wins (like for P4Runtime) is hard-coded *)
      SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
    | NONE => NONE)
End

val _ = export_theory ();
