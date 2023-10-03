open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4Syntax p4_auxTheory p4_coreTheory p4_coreLib;

val _ = new_theory "p4_v1model";

(* Useful documentation and reference links:
   https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md
   https://github.com/p4lang/behavioral-model/blob/main/targets/simple_switch/simple_switch.cpp
*)

(* TODO: v1model uses a checksum in the verify_checksum and update_checksum externs *)
Datatype:
 v1model_v_ext =
   v1model_v_ext_ipv4_checksum (word16 list)
 | v1model_v_ext_counter
 | v1model_v_ext_direct_counter
 | v1model_v_ext_meter
 | v1model_v_ext_direct_meter
 | v1model_v_ext_register ((bool list # num) list)
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

Definition v1model_ascope_update_v_map_def:
 v1model_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition v1model_packet_in_extract:
 v1model_packet_in_extract = packet_in_extract_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_in_lookahead:
 v1model_packet_in_lookahead = packet_in_lookahead_gen v1model_ascope_lookup v1model_ascope_update_v_map
End

Definition v1model_packet_in_advance:
 v1model_packet_in_advance = packet_in_advance_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_out_emit:
 v1model_packet_out_emit = packet_out_emit_gen v1model_ascope_lookup v1model_ascope_update
End

Definition v1model_verify:
 (v1model_verify (ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen v1model_ascope_update_v_map (ascope, g_scope_list, scope_list))
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* NOTE: 511 is the default drop port *)
Definition v1model_mark_to_drop_def:
 v1model_mark_to_drop (v1model_ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case assign scope_list (v_bit (fixwidth 9 (n2v 511), 9)) (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") of
   | SOME scope_list' =>
    (case assign scope_list' (v_bit (fixwidth 16 (n2v 0), 16)) (lval_field (lval_varname (varn_name "standard_metadata")) "mcast_grp") of
     | SOME scope_list'' =>
      SOME (v1model_ascope, scope_list'', status_returnv v_bot)
     | NONE => NONE)
   | NONE => NONE
End

(**********************)
(* Checksum methods   *)
(**********************)

(*************************)
(* TODO: verify_checksum *)

(*************************)
(* TODO: update_checksum *)

(**************)
(* Register   *)
(**************)

Definition replicate_arb:
 replicate_arb length width =
  REPLICATE length ((REPLICATE width (ARB:bool)), width)
End

Definition Register_construct:
 (Register_construct ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "size")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "targ1")) of
    | SOME (v_bit (bl', n')) =>
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_register (replicate_arb (v2n bl) n'))) in
     (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition Register_read:
 (Register_read ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (case oEL (v2n bl) array of
        | SOME (bl', n') =>
         (case assign scope_list (v_bit (bl', n')) (lval_varname (varn_name "result")) of
          | SOME scope_list' =>
           SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)
          | NONE => NONE)
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition Register_write:
 (Register_write ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "value")) of
    | SOME (v_bit (bl', n')) =>
     (case lookup_lval scope_list (lval_varname (varn_name "this")) of
      | SOME (v_ext_ref i) =>
       (case ALOOKUP ext_obj_map i of
        | SOME (INR (v1model_v_ext_register array)) =>
         let array' = LUPDATE (bl', n') (v2n bl) array in
         let ext_obj_map' = AUPDATE ext_obj_map (i, INR (v1model_v_ext_register array')) in
          SOME ((counter, ext_obj_map', v_map, ctrl), scope_list, status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: The reset values of standard metadata *)
val v1model_standard_metadata_zeroed =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(``"ingress_port"``, mk_v_bitii (0, 9)),
    (``"egress_spec"``, mk_v_bitii (0, 9)),
    (``"egress_port"``, mk_v_bitii (0, 9)),
    (``"instance_type"``, mk_v_bitii (0, 32)),
    (``"packet_length"``, mk_v_bitii (0, 32)),
    (``"enq_timestamp"``, mk_v_bitii (0, 32)),
    (``"enq_qdepth"``, mk_v_bitii (0, 19)),
    (``"deq_timedelta"``, mk_v_bitii (0, 32)),
    (``"deq_qdepth"``, mk_v_bitii (0, 19)),
    (``"ingress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"egress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"mcast_grp"``, mk_v_bitii (0, 16)),
    (``"egress_rid"``, mk_v_bitii (0, 16)),
    (``"checksum_error"``, mk_v_bitii (0, 1)),
    (``"parser_error"``, mk_v_bitii (0, 32)),
    (``"priority"``, mk_v_bitii (0, 3))],
   “:(string # v)”);

val v1model_init_ext_obj_map = “[(0, INL (core_v_ext_packet []));
                                 (1, INL (core_v_ext_packet []))]:(num, v1model_sum_v_ext) alist”;

val v1model_init_counter = rhs $ concl $ EVAL “LENGTH ^v1model_init_ext_obj_map”;

(*
val v1model_standard_metadata_uninit =
 mk_v_struct_list [(``"ingress_port"``, mk_v_biti_arb 9),
                   (``"egress_spec"``, mk_v_biti_arb 9),
                   (``"egress_port"``, mk_v_biti_arb 9),
                   (``"instance_type"``, mk_v_biti_arb 32),
                   (``"packet_length"``, mk_v_biti_arb 32),
                   (``"enq_timestamp"``, mk_v_biti_arb 32),
                   (``"enq_qdepth"``, mk_v_biti_arb 19),
                   (``"deq_timedelta"``, mk_v_biti_arb 32),
                   (``"deq_qdepth"``, mk_v_biti_arb 19),
                   (``"ingress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"egress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"mcast_grp"``, mk_v_biti_arb 16),
                   (``"egress_rid"``, mk_v_biti_arb 16),
                   (``"checksum_error"``, mk_v_biti_arb 1),
                   (``"parser_error"``, mk_v_biti_arb 32),
                   (``"priority"``, mk_v_biti_arb 3)];
*)
(*
val v1model_meta_uninit =
 mk_v_struct_list [];

val v1model_row_uninit =
 mk_v_struct_list [(``"e"``, mk_v_biti_arb 8),
                   (``"t"``, mk_v_biti_arb 16),
                   (``"l"``, mk_v_biti_arb 8),
                   (``"r"``, mk_v_biti_arb 8),
                   (``"v"``, mk_v_biti_arb 8)];

val v1model_hdr_uninit =
 mk_v_header_list F [(``"row"``, v1model_row_uninit)];

val v1model_header_uninit =
 mk_v_struct_list [(``"h"``, v1model_hdr_uninit)];
*)
val v1model_init_v_map = ``^core_init_v_map ++
                           [("b", v_ext_ref 0);
                            ("b_temp", v_ext_ref 1)]:(string, v) alist``;

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition v1model_input_f_def:
 (v1model_input_f (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, all extern objects are wiped. This need not be the case *)
   let counter' = ^v1model_init_counter in
   let ext_obj_map' = AUPDATE ^v1model_init_ext_obj_map (0, INL (core_v_ext_packet bl)) in
   let v_map' = AUPDATE_LIST ^v1model_init_v_map [("standard_metadata", v_struct (AUPDATE (^v1model_standard_metadata_zeroed) ("ingress_port", v_bit (w9 (n2w p)))));
                                                  ("parsedHdr", tau1_uninit_v);
                                                  ("hdr", tau1_uninit_v);
                                                  ("meta", tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope))
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
 v1model_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case v1model_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition v1model_copyout_pbl_def:
 v1model_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
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

(* Transfers the value of parsedHdr to hdr and the parserError value to standard_metadata,
 * then resets the shared packet "b" (TODO: Fix that hack) and saves its content in "b_temp" *)
Definition v1model_postparser_def:
 v1model_postparser ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case ALOOKUP v_map "b" of
   | SOME (v_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map "b_temp" of
       | SOME (v_ext_ref i') =>
        (case ALOOKUP v_map "parsedHdr" of
         | SOME v =>
          let v_map' = AUPDATE v_map ("hdr", v) in
           (case ALOOKUP v_map "parseError" of
            | SOME v' =>
             (case assign [v_map_to_scope v_map'] v' (lval_field (lval_varname (varn_name "standard_metadata")) "parser_error") of
              | SOME [v_map_scope] =>
               (case scope_to_vmap v_map_scope of
                | SOME v_map'' =>
                 let (counter', ext_obj_map', v_map''', ctrl') = (v1model_ascope_update (counter, ext_obj_map, v_map'', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (v1model_ascope_update (counter', ext_obj_map', v_map''', ctrl') i (INL (core_v_ext_packet [])))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
Definition v1model_output_f_def:
 v1model_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case v1model_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case v1model_lookup_obj ext_obj_map v_map "b_temp" of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map "standard_metadata" of
       | SOME (v_struct struct) =>
        (case ALOOKUP struct "egress_spec" of
         | SOME (v_bit (port_bl, n)) =>
          let port_out = v2n port_bl in
           if port_out = 511
           then SOME (in_out_list, (counter, ext_obj_map, v_map, ctrl))
           else SOME (in_out_list++[(bl++bl', port_out)], (counter, ext_obj_map, v_map, ctrl))
         | _ => NONE)
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
