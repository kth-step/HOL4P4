open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4Syntax p4_auxTheory p4_coreTheory p4_coreLib;

val _ = new_theory "p4_psa";

(* Useful documentation and reference links:
   https://github.com/p4lang/p4c/blob/main/p4include/bmv2/psa.p4
   https://p4.org/p4-spec/docs/PSA.html
*)

(* TODO: Implement more extern objects *)
Datatype:
 psa_v_ext =
   psa_v_ext_packet_replication_engine
 | psa_v_ext_buffering_queueing_engine
 | psa_v_ext_hash
 | psa_v_ext_checksum
 | psa_v_ext_internet_checksum (word16 list)
 | psa_v_ext_counter
 | psa_v_ext_direct_counter
 | psa_v_ext_meter
 | psa_v_ext_direct_meter
 | psa_v_ext_register
 | psa_v_ext_random
 | psa_v_ext_action_profile
 | psa_v_ext_action_selector
 | psa_v_ext_digest
End
val _ = type_abbrev("psa_sum_v_ext", ``:(core_v_ext, psa_v_ext) sum``);

val _ = type_abbrev("psa_ctrl", ``:(string, (e_list, string # e_list) alist) alist``);

(* The architectural state type of the PSA model *)
val _ = type_abbrev("psa_ascope", ``:(num # ((num, psa_sum_v_ext) alist) # ((string, v) alist) # psa_ctrl)``);

(* TODO: These are target-specific and can not be preset in general - have to be read from psa.p4 and
 * stored in v_map *)
(*
val psa_port_recirculate = “4294967290:num”;
val psa_port_cpu = “4294967293:num”;
*)

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition psa_ascope_lookup_def:
 psa_ascope_lookup (ascope:psa_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition psa_ascope_update_def:
 psa_ascope_update ((counter, ext_obj_map, v_map, ctrl):psa_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition psa_ascope_update_v_map_def:
 psa_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):psa_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition psa_packet_in_extract:
 psa_packet_in_extract = packet_in_extract_gen psa_ascope_lookup psa_ascope_update psa_ascope_update_v_map
End

Definition psa_packet_in_lookahead:
 psa_packet_in_lookahead = packet_in_lookahead_gen psa_ascope_lookup psa_ascope_update_v_map
End

Definition psa_packet_in_advance:
 psa_packet_in_advance = packet_in_advance_gen psa_ascope_lookup psa_ascope_update psa_ascope_update_v_map
End

Definition psa_packet_out_emit:
 psa_packet_out_emit = packet_out_emit_gen psa_ascope_lookup psa_ascope_update
End

Definition psa_verify:
 (psa_verify (ascope:psa_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen psa_ascope_update_v_map (ascope, g_scope_list, scope_list))
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* TODO: psa_clone_i2e *)

(* TODO: psa_resubmit *)

(* TODO: psa_normal *)

(* TODO: psa_clone_e2e *)

(* TODO: psa_recirculate *)

(* TODO: assert *)

(* TODO: assume *)

(******************************)
(* InternetChecksum methods   *)
(******************************)

(*************)
(* construct *)

Definition InternetChecksum_construct:
 (InternetChecksum_construct ((counter, ext_obj_map, v_map, ctrl):psa_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (psa_v_ext_internet_checksum ([]:word16 list))) in
  (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
   | NONE => NONE)
 )
End


(*******)
(* add *)

Definition InternetChecksum_add:
 (InternetChecksum_add ((counter, ext_obj_map, v_map, ctrl):psa_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (psa_v_ext_internet_checksum ipv4_checksum)) =>
     (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_obj_map (i, INR (psa_v_ext_internet_checksum (ipv4_checksum ++ checksum_incr))), v_map, ctrl), scope_list, status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(*******)
(* get *)

Definition InternetChecksum_get:
 (InternetChecksum_get ((counter, ext_obj_map, v_map, ctrl):psa_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (psa_v_ext_internet_checksum ipv4_checksum)) =>
     SOME ((counter, ext_obj_map, v_map, ctrl):psa_ascope, scope_list, status_returnv (v_bit (w16 (compute_checksum16 ipv4_checksum))))
    | _ => NONE)
  | _ => NONE
 )
End


(***********************************************)
(* TODO: clear, subtract, get_state, set_state *)


(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: Note that this assumes the widths of some types, which are target-specific *)

(***********************)
(* Architectural state *)

val psa_init_ext_obj_map = “[(0, INL (core_v_ext_packet []));
                             (1, INL (core_v_ext_packet []))]:(num, psa_sum_v_ext) alist”;

val psa_init_counter = rhs $ concl $ EVAL “LENGTH ^psa_init_ext_obj_map”;

(* TODO: packet_path, parser_error are enum values, here serialised to 32 bits *)
val psa_ingress_parser_input_metadata_t =
 mk_tau_header
  [("ingress_port", mk_tau_bit 32),
   ("packet_path", mk_tau_bit 32)];
val psa_ingress_parser_input_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_ingress_parser_input_metadata_t”;

val psa_ingress_input_metadata_t =
 mk_tau_header
  [("ingress_port", mk_tau_bit 32),
   ("packet_path", mk_tau_bit 32),
   ("ingress_timestamp", mk_tau_bit 64),
   ("parser_error", mk_tau_bit 32)];
val psa_ingress_input_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_ingress_input_metadata_t”;


val psa_ingress_output_metadata_t =
 mk_tau_header
  [("class_of_service", mk_tau_bit 8),
   ("clone", tau_bool_tm),
   ("clone_session_id", mk_tau_bit 16),
   ("drop", tau_bool_tm),
   ("resubmit", tau_bool_tm),
   ("multicast_group", mk_tau_bit 32),
   ("egress_port", mk_tau_bit 32)];
val psa_ingress_output_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_ingress_output_metadata_t”;
val psa_ingress_output_metadata_t_initial_v =
  mk_v_header_list (F,
   [("class_of_service", mk_v_bitii (0, 8)),
    ("clone", mk_v_bool F),
    ("clone_session_id", mk_v_biti_arb 16),
    ("drop", mk_v_bool T),
    ("resubmit", mk_v_bool F),
    ("multicast_group", mk_v_bitii (0, 32)),
    ("egress_port", mk_v_biti_arb 32)];)



val psa_egress_parser_input_metadata_t =
 mk_tau_header
  [("egress_port", mk_tau_bit 32),
   ("packet_path", mk_tau_bit 32)];
val psa_egress_parser_input_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_egress_parser_input_metadata_t”;

val psa_egress_input_metadata_t =
 mk_tau_header
  [("class_of_service", mk_tau_bit 8),
   ("egress_port", mk_tau_bit 32),
   ("packet_path", mk_tau_bit 32),
   ("instance", mk_tau_bit 16),
   ("egress_timestamp", mk_tau_bit 64),
   ("parser_error", mk_tau_bit 32)];
val psa_egress_input_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_egress_input_metadata_t”;

val psa_egress_output_metadata_t =
 mk_tau_header
  [("clone", tau_bool_tm),
   ("clone_session_id", mk_tau_bit 16),
   ("drop", tau_bool_tm)];
val psa_egress_output_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_egress_output_metadata_t”;

val psa_egress_deparser_input_metadata_t =
 mk_tau_header
  [("egress_port", mk_tau_bit 32)];
val psa_egress_deparser_input_metadata_t_uninit_v = rhs $ concl $ EVAL “arb_from_tau ^psa_egress_deparser_input_metadata_t”;

val psa_init_v_map = “^core_init_v_map ++
                        [("pkt", v_ext_ref 0);
                         ("pkt_temp", v_ext_ref 1)]:(string, v) alist”;

(* TODO: This should perhaps also arbitrate between different ports, taking a list of lists of input *)
(* Note: This step only declares variables for the ingress, and so takes only IH, IM, NM, CI2EM, RESUBM and RECIRCM init values *)
Definition psa_input_f_def:
 (psa_input_f (tau1_uninit_v,tau2_uninit_v,tau3_uninit_v,tau4_uninit_v,tau5_uninit_v,tau6_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, all extern objects are wiped. This need not be the case in general *)
   let counter' = ^psa_init_counter in
   let ext_obj_map' = AUPDATE ^psa_init_ext_obj_map (0, INL (core_v_ext_packet bl)) in
   let v_map' = AUPDATE_LIST ^psa_init_v_map [("parsed_hdr", tau1_uninit_v);
                                              ("hdr", tau1_uninit_v);
                                              ("user_meta", tau2_uninit_v);
                                              ("normal_meta", tau3_uninit_v);
                                              ("meta", tau2_uninit_v);
                                              ("resubmit_meta", tau4_uninit_v);
                                              ("recirculate_meta", tau5_uninit_v);
                                              ("clone_i2e_meta", tau6_uninit_v);
                                              ("istd", ^psa_ingress_parser_input_metadata_t_uninit_v);
                                              ("ostd", ^psa_ingress_output_metadata_t_initial_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):psa_ascope))
End

(* TODO: Generalise and move to core? Duplicated in all architectures... *)
Definition psa_reduce_nonout_def:
 (psa_reduce_nonout ([], elist, v_map) =
  SOME []
 ) /\
 (psa_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, psa_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, psa_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v v), psa_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (psa_reduce_nonout (_, _, v_map) = NONE)
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
Definition psa_copyin_pbl_def:
 psa_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  case psa_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition psa_copyout_pbl_def:
 psa_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):psa_ascope, dlist, xlist, (status:status)) =
  case copyout xlist dlist [ [] ; [] ] [v_map_to_scope v_map] g_scope_list of
  | SOME (_, [v_map_scope]) =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):psa_ascope)
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Make generic *)
Definition psa_lookup_obj_def:
 psa_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* TODO: Should transfer the parserError to ingress from_parser metadata *)
Definition psa_post_ingressparser_def:
 psa_post_ingressparser ((counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  SOME (counter, ext_obj_map, v_map, ctrl)
End

Definition psa_post_ingress_def:
 psa_post_ingress ((counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  (case ALOOKUP v_map "user_meta" of
   | SOME v =>
    let v_map' = AUPDATE v_map ("meta", v) in
     SOME (counter, ext_obj_map, v_map', ctrl)
   | NONE => NONE)
End

Definition psa_post_ingressdeparser_def:
 psa_post_ingressdeparser (tau1_uninit_v,tau2_uninit_v,tau3_uninit_v,tau4_uninit_v,tau5_uninit_v,tau6_uninit_v) ((counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  (case ALOOKUP ext_obj_map 0 of
   | SOME (INL (core_v_ext_packet bl)) =>
    let ext_obj_map' = AUPDATE_LIST ^psa_init_ext_obj_map [(0, INL (core_v_ext_packet []));
                                                           (1, INL (core_v_ext_packet bl))] in
    (* TODO: Add transfer of metadata *)
    let v_map' = AUPDATE_LIST ^psa_init_v_map [("parsed_hdr", tau1_uninit_v);
                                               ("hdr", tau1_uninit_v);
                                               ("user_meta", tau2_uninit_v);
                                               ("normal_meta", tau3_uninit_v);
                                               ("meta", tau2_uninit_v);
                                               ("clone_i2e_meta", tau4_uninit_v);
                                               ("clone_e2e_meta", tau5_uninit_v);
                                               ("recirculate_meta", tau6_uninit_v);
                                               ("istd", ^psa_egress_parser_input_metadata_t_uninit_v);
                                               ("ostd", ^psa_egress_output_metadata_t_uninit_v)] in
    SOME (counter, ext_obj_map', v_map', ctrl)
   | _ => NONE)
End

(* TODO: Should transfer the parserError to egress from_parser metadata *)
Definition psa_post_egressparser_def:
 psa_post_egressparser ((counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  SOME (counter, ext_obj_map, v_map, ctrl)
End

Definition psa_post_egress_def:
 psa_post_egress ((counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  (case ALOOKUP v_map "user_meta" of
   | SOME v =>
    let v_map' = AUPDATE v_map ("meta", v) in
     SOME (counter, ext_obj_map, v_map', ctrl)
   | NONE => NONE)
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
Definition psa_output_f_def:
 psa_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):psa_ascope) =
  (case psa_lookup_obj ext_obj_map v_map "buffer" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case psa_lookup_obj ext_obj_map v_map "buffer_temp" of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map "ostd" of
       | SOME (v_struct struct) =>
        (case ALOOKUP struct "egress_port" of
         | SOME (v_bit (port_bl, n)) =>
          let port_out = v2n port_bl in
           (* Default drop port *)
           if port_out = 511
           then SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
           else SOME (in_out_list++[(bl++bl', port_out)], (counter, ext_obj_map, v_map, ctrl))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

Definition psa_apply_table_f_def:
 psa_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):psa_ascope) =
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
