open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory p4_coreTheory;

val _ = new_theory "p4_vss";

val _ = Hol_datatype ` 
 vss_v_ext = vss_v_ext_ipv4_checksum of word16`;
val _ = type_abbrev("v_ext", ``:(core_v_ext, vss_v_ext) sum``);

(* TODO: Fix this *)
val _ = type_abbrev("vss_ctrl", ``:scope``);

(* The architectural scope type of the VSS architecture model *)
val _ = type_abbrev("vss_ascope", ``:(num # ((num, v_ext) alist) # ((string, num) alist) # vss_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition vss_ascope_lookup_def:
 vss_ascope_lookup (ascope:vss_ascope) ext_ref = 
  let ext_map = FST $ SND ascope in
   ALOOKUP ext_map ext_ref
End

Definition vss_ascope_update_def:
 vss_ascope_update ((counter, ext_map, ref_map, ctrl):vss_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_map (ext_ref, v_ext), ref_map, ctrl)
End

Definition packet_in_extract:
 packet_in_extract = packet_in_extract_gen vss_ascope_lookup vss_ascope_update
End

Definition packet_out_emit:
 packet_out_emit = packet_out_emit_gen vss_ascope_lookup vss_ascope_update
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
 (Checksum16_construct ((counter, ext_map, ref_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_map' = AUPDATE ext_map (counter, INR (vss_v_ext_ipv4_checksum (0w:word16))) in
  (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_map', ref_map, ctrl), g_scope_list, scope_list)
   | NONE => NONE)
 )
End


(*********)
(* clear *)

Definition Checksum16_clear:
 (Checksum16_clear ((counter, ext_map, ref_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   SOME ((counter, AUPDATE ext_map (i, INR (vss_v_ext_ipv4_checksum (0w:word16))), ref_map, ctrl), g_scope_list, scope_list)
  | _ => NONE
 )
End


(**********)
(* update *)

(* TODO: Add recursive cases *)
Definition header_entry2v:
 (header_entry2v (x:x, v) =
  case v of
  | (v_bit (bl, n)) => SOME bl
  | _ => NONE
 )
End

Definition header_entries2v:
 (header_entries2v [] = SOME []) /\
 (header_entries2v (h::t) =
  case header_entry2v h of
  | SOME bl =>
  (case header_entries2v t of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 )
End


TotalDefn.tDefine "v2w16s'" `
 (v2w16s' [] = []) /\
 (v2w16s' v =
  ((v2w (TAKE 16 v)):word16)::(v2w16s' (DROP 16 v))
 )`
(WF_REL_TAC `measure LENGTH` >>
 fs []);

Definition v2w16s:
 (v2w16s v = if (LENGTH v) MOD 16 = 0 then SOME (v2w16s' v) else NONE)
End

Definition get_checksum_incr:
 (get_checksum_incr scope_list ext_data_name =
   (case lookup_lval scope_list ext_data_name of
    | SOME (v_bit (bl, n)) => if n = 16 then SOME ((v2w bl):word16) else NONE
    | SOME (v_header vbit h_list) =>
     (case header_entries2v h_list of
      | SOME bl =>
       (case v2w16s bl of
	| SOME w16s => SOME (FOLDL word_add (0w) w16s)
	| NONE => NONE)
      | NONE => NONE)
    | _ => NONE)
 )
End

(* Note that this assumes the order of fields in the header is correct *)
(* TODO: Check for overflow, compensate according to IPv4 checksum algorithm *)
Definition Checksum16_update:
 (Checksum16_update ((counter, ext_map, ref_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_map (i, INR (vss_v_ext_ipv4_checksum (word_1comp (ipv4_checksum + checksum_incr)))), ref_map, ctrl), g_scope_list, scope_list)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(*******)
(* get *)

Definition Checksum16_get:
 (Checksum16_get ((counter, ext_map, ref_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     SOME ((counter, ext_map, ref_map, ctrl):vss_ascope, g_scope_list:g_scope_list, initialise scope_list varn_ext_ret (v_bit (w16 ipv4_checksum)))
    | _ => NONE)
  | _ => NONE
 )
End


(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: This should arbitrate between different ports, taking a list of lists of input *)
(* NOTE: the model starts out at the data link layer *)
(* https://en.wikipedia.org/wiki/Ethernet_frame#Frame_%E2%80%93_data_link_layer *)
(* 1. Read into header to determine size of packet *)
(*    Technically, you would look into EtherType first, to determine
 *    whether it is used for payload size or protocol ID.
 *    We always have IPv4, so need to look into IPv4 header.
 *    Also, no 802.1Q tag is assumed. This would have been known
 *    from the bits normally forming the EtherType field having the
 *    value 0x8100 instead of 0x8000 (IPv4). *)
(* 2. Remove data + Ethernet CRC *)
(* 3. Put the rest of the header into the input extern object *)
(* TODO: Also take different values of IHL into account *)
(* Length of both headers 112+160=272 (IHL=5 assumed) *)
(* TODO: Make smarter extract function for getting total_length *)
(* let total_length = (v2n (REVERSE (TAKE 16 (REVERSE (TAKE 144 h)))))*8 in *)
(* TODO: Fix this. *)
val vss_input_f_def = Define `
  (vss_input_f (io_list:in_out_list, (counter, ext_map, ref_map, ctrl):vss_ascope) =
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let header = TAKE 272 bl in
    let data_crc = REVERSE (DROP 272 (REVERSE bl)) in
    let ext_map' = AUPDATE ext_map (counter, header) in
    (case ALOOKUP ref_map "b" of
     | SOME i =>
      let ext_map'' = AUPDATE ref_map (i, INL (core_v_ext_packet_in header)) in
      (case ALOOKUP ref_map "data_crc" of
       | SOME i' =>
        let ext_map''' = AUPDATE ext_map (i', INL (core_v_ext_packet_out data_crc)) in
        (* TODO: Assign to inCtrl. Should we also give global scope as a vss_input_f argument? *)
     (io_list:in_out_list, (counter, ext_map'', ref_map, ctrl):vss_ascope)

(*
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let header = TAKE 272 bl in
    let data_crc = REVERSE (DROP 272 (REVERSE bl)) in
    (case assign [scope] (v_ext (ext_obj_in header)) (lval_varname (varn_name "b")) of
     | SOME [scope'] =>
      (case assign [scope'] (v_ext (ext_obj_out data_crc)) (lval_varname (varn_name "data_crc")) of
       | SOME [scope''] =>
        (case assign [scope''] (v_bit (fixwidth 4 (n2v p), 4)) (lval_field (lval_varname (varn_name "inCtrl")) "inputPort") of
         | SOME [scope'''] => SOME (t, scope''')
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
*)
  )
`;

val vss_reduce_nonout_def = Define `
 (vss_reduce_nonout ([], elist, vss_ascope) =
  SOME []
 ) /\
 (vss_reduce_nonout (d::dlist, e::elist, vss_ascope) =
  if is_d_out d
  then oCONS (e, vss_reduce_nonout (dlist, elist, vss_ascope))
  else
   (case e of
    | (e_var x) =>
     (case lookup_vexp2 [ [] ] [vss_ascope] x of
      | SOME v => oCONS (e_v v, vss_reduce_nonout (dlist, elist, vss_ascope))
      | NONE => NONE)
    | _ => NONE) 
 )
`;

(* TODO: Since this should be initialised
 *       for all architectures, maybe it should be outsourced to a
 *       architecture-generic function? *)
val vss_copyin_pbl_def = Define `
  vss_copyin_pbl (xlist, dlist, elist, vss_ascope, pbl_type) =
    case vss_reduce_nonout (dlist, elist, vss_ascope) of
    | SOME elist' =>
      (case copyin xlist dlist elist' [vss_ascope] [ [] ] of
       | SOME scope =>
         if pbl_type = pbl_type_parser
         then
           SOME (initialise_parse_error scope)
         else
           SOME scope
       | NONE => NONE)
    | NONE => NONE
`;

(* TODO: Does anything need to be looked up for this function? *)
(* TODO: pbl_type-dependent behaviour *)
(* Note that this re-uses the copyout function intended for P4 functions *)
val vss_copyout_pbl_def = Define `
  vss_copyout_pbl (ss, vss_ascope, dlist, xlist, pbl_type, (status:status)) =
    case copyout xlist dlist [ [] ; [] ] [vss_ascope] ss of
    | SOME (g_scope_list, [vss_ascope']) =>
      if pbl_type = pbl_type_parser
      then
        (case lookup_lval ss (lval_varname (varn_name "parseError")) of
         | SOME v =>
           (case assign [vss_ascope'] v (lval_varname (varn_name "parseError")) of
            | SOME [vss_ascope''] => SOME vss_ascope''
            | NONE => NONE)
         | _ => NONE)
      else
       SOME vss_ascope'
    | _ => NONE
`;


val vss_parser_runtime_def = Define `
  vss_parser_runtime (scope:vss_ascope) =
   (case lookup_lval [scope] (lval_varname (varn_name "parsedHeaders")) of
    | SOME (v_struct hdrs) =>
       (case assign [scope] (v_struct hdrs) (lval_varname (varn_name "headers")) of
        | SOME [scope'] => SOME scope'
        | _ => NONE)
    | _ => NONE)
`;

val vss_pre_deparser_def = Define `
  vss_pre_deparser (scope:vss_ascope) =
   (case lookup_lval [scope] (lval_varname (varn_name "headers")) of
    | SOME (v_struct hdrs) =>
      (case assign [scope] (v_struct hdrs) (lval_varname (varn_name "outputHeaders")) of
       | SOME [scope'] => SOME scope'
       | _ => NONE)
    | _ => NONE)
`;

(* Add new header + data + Ethernet CRC as a tuple with new output port to output list *)
(* Add data + Ethernet CRC *)
(* TODO: Outsource obtaining the output port to an external function? *)
(* TODO: Fix this *)
val vss_output_f_def = Define `
 vss_output_f (in_out_list:in_out_list, scope:vss_ascope) =
(*
  (case lookup_lval [scope] (lval_varname (varn_name "b")) of
   | SOME (v_ext (ext_obj_in headers)) =>
    (case lookup_lval [scope] (lval_varname (varn_name "data_crc")) of
     | SOME (v_ext (ext_obj_out data_crc)) =>
      (case lookup_lval [scope] (lval_varname (varn_name "outCtrl")) of
       | SOME (v_struct [(fldname, v_bit (bl, n))]) =>
        SOME (in_out_list++[(headers++data_crc, v2n bl)], scope)
       | _ => NONE
      )
     | _ => NONE
    )
   | _ => NONE
  )
*)
  SOME (in_out_list:in_out_list, scope:vss_ascope)
`;

(*

val copyin_pbl_def = Define `
  copyin_pbl xlist dlist elist gsl ss_curr =
    let
     (* MAP if_is_red*)
    in
      all_arg_update_for_newscope xlist dlist elist' (gsl++ss_curr)
    end
`;

*)

val _ = export_theory ();
