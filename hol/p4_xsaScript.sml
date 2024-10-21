open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4Syntax p4_auxTheory p4_coreTheory p4_coreLib;

val _ = new_theory "p4_xsa";

(* TODO: Link to documentation *)

(* TODO: NOTE ON CONTROL PLANE API? *)

(* TODO: Add externs *)
Datatype:
 xsa_v_ext =
   xsa_v_ext_example
End
val _ = type_abbrev("xsa_sum_v_ext", ``:(core_v_ext, xsa_v_ext) sum``);

(* The control plane representation:

   (* the table name *)
   (string, 
     (* the key of a table entry: first element is a predicate for matching, second is priority *)
    ((e_list -> bool, num),
     (* the action of a table entry: string is action name, e_list is arguments *)
     string # e_list) alist) alist``)
*)
val _ = type_abbrev("xsa_ctrl", ``:(string, (((e_list -> bool) # num), string # e_list) alist) alist``);

(* The architectural state type of the xsa architecture model *)
val _ = type_abbrev("xsa_ascope", ``:(num # ((num, xsa_sum_v_ext) alist) # ((string, v) alist) # xsa_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition xsa_ascope_lookup_def:
 xsa_ascope_lookup (ascope:xsa_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition xsa_ascope_update_def:
 xsa_ascope_update ((counter, ext_obj_map, v_map, ctrl):xsa_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition xsa_ascope_update_v_map_def:
 xsa_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):xsa_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition xsa_packet_in_extract_def:
 xsa_packet_in_extract = packet_in_extract_gen xsa_ascope_lookup xsa_ascope_update xsa_ascope_update_v_map
End

Definition xsa_packet_in_lookahead_def:
 xsa_packet_in_lookahead = packet_in_lookahead_gen xsa_ascope_lookup xsa_ascope_update_v_map
End

Definition xsa_packet_in_advance_def:
 xsa_packet_in_advance = packet_in_advance_gen xsa_ascope_lookup xsa_ascope_update xsa_ascope_update_v_map
End

Definition xsa_packet_out_emit_def:
 xsa_packet_out_emit = packet_out_emit_gen xsa_ascope_lookup xsa_ascope_update
End

Definition xsa_verify_def:
 (xsa_verify (ascope:xsa_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen xsa_ascope_update_v_map (ascope, g_scope_list, scope_list))
End

(**********************************************)
(*             HELPER FUNCTIONS               *)
(**********************************************)

Definition xsa_ascope_read_ext_obj_def:
 xsa_ascope_read_ext_obj ((counter, ext_obj_map, v_map, ctrl):xsa_ascope) vname =
  case ALOOKUP v_map vname of
  | SOME (v_ext_ref n) =>
   ALOOKUP ext_obj_map n
  | _ => NONE
End

Definition xsa_ascope_of_conc_state_def:
 xsa_ascope_of_conc_state (io1,io2,(ascope:xsa_ascope)) =
  ascope
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* TODO: xsa counterpart?
(* NOTE: 511 is the default drop port *)
Definition xsa_mark_to_drop_def:
 xsa_mark_to_drop (xsa_ascope:xsa_ascope, g_scope_list:g_scope_list, scope_list) =
  case assign scope_list (v_bit (fixwidth 9 (n2v 511), 9)) (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") of
   | SOME scope_list' =>
    (case assign scope_list' (v_bit (fixwidth 16 (n2v 0), 16)) (lval_field (lval_varname (varn_name "standard_metadata")) "mcast_grp") of
     | SOME scope_list'' =>
      SOME (xsa_ascope, scope_list'', status_returnv v_bot)
     | NONE => NONE)
   | NONE => NONE
End
*)

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: XSA standard metadata *)
val xsa_standard_metadata_zeroed =
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

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition xsa_input_f_def:
 (xsa_input_f (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):xsa_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   (* let counter' = ^xsa_init_counter in *)
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [("b", v_ext_ref counter);
                                    ("b_temp", v_ext_ref (counter+1));
                                    ("standard_metadata", v_struct (AUPDATE (^xsa_standard_metadata_zeroed) ("ingress_port", v_bit (w9 (n2w p)))));
                                    ("parsedHdr", tau1_uninit_v);
                                    ("hdr", tau1_uninit_v);
                                    ("meta", tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):xsa_ascope))
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition xsa_reduce_nonout_def:
 (xsa_reduce_nonout ([], elist, v_map) =
  SOME []
 ) /\
 (xsa_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, xsa_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, xsa_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v v), xsa_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (xsa_reduce_nonout (_, _, v_map) = NONE)
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
Definition xsa_copyin_pbl_def:
 xsa_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):xsa_ascope) =
  case xsa_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition xsa_copyout_pbl_def:
 xsa_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):xsa_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):xsa_ascope)
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Make generic *)
Definition xsa_lookup_obj_def:
 xsa_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* Transfers the value of parsedHdr to hdr and the parserError value to standard_metadata,
 * then resets the shared packet "b" (TODO: Fix that hack) and saves its content in "b_temp" *)
(* TODO: Note that this also resets parseError to 0 *)
Definition xsa_postparser_def:
 xsa_postparser ((counter, ext_obj_map, v_map, ctrl):xsa_ascope) =
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
                 let v_map''' = AUPDATE v_map'' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl') = (xsa_ascope_update (counter, ext_obj_map, v_map''', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (xsa_ascope_update (counter', ext_obj_map', v_map'''', ctrl') i (INL (core_v_ext_packet [])))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

(* Note that this split-up of functions is so that the symbolic execution
 * can handle symbolic branch on output port.
 * TODO: Use the v directly (and not the port_bl) in order to
 * make sense to also use as a control plane assumption, specifically on
 * the argument of an action. *)
Definition xsa_is_drop_port_def:
 xsa_is_drop_port port_bl =
  if v2n port_bl = 511
  then T
  else F
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
(* A little clumsy with the double v2n, but that makes things easier *)
Definition xsa_output_f_def:
 xsa_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):xsa_ascope) =
  (case xsa_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case xsa_lookup_obj ext_obj_map v_map "b_temp" of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map "standard_metadata" of
       | SOME (v_struct struct) =>
        (case ALOOKUP struct "egress_spec" of
         | SOME (v_bit (port_bl, n)) =>
          SOME (in_out_list++(if xsa_is_drop_port port_bl then [] else [(bl++bl', v2n port_bl)]), (counter, ext_obj_map, v_map, ctrl))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End  

(* This assumes that tables contains at most one LPM key,
 * with other keys being exact if one LPM key is present.
 * Note that table priority is runtime-dependent, with only partial P4 language
 * support. *)
(* TODO: P4Runtime API? *)
val xsa_apply_table_f_def = xDefine "xsa_apply_table_f"
  ‘xsa_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):xsa_ascope) =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      (* Largest priority wins *)
      SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
     | NONE => NONE’;

val _ = export_theory ();
