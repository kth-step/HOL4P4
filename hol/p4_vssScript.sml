open HolKernel boolLib Parse bossLib ottLib;

val _ = new_theory "p4_vss";

open p4Theory p4_auxTheory p4_coreTheory;
    
Datatype:
 vss_v_ext =
   vss_v_ext_ipv4_checksum ((bool list) list)
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

Definition Checksum16_construct_def:
 (Checksum16_construct ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (vss_v_ext_ipv4_checksum ([]:(bool list) list))) in
  (case assign' scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
   | NONE => NONE)
 )
End


(*********)
(* clear *)

Definition Checksum16_clear_def:
 (Checksum16_clear ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum ([]:(bool list) list))), v_map, ctrl), scope_list, status_returnv v_bot)
  | _ => NONE
 )
End


(**********)
(* update *)

Definition v2w16s'''_def:
 (v2w16s''' [] = SOME []) /\
 (v2w16s''' v =
  case oTAKE_DROP 16 v of
  | SOME (taken, left) =>
   (case v2w16s''' left of
    | SOME l =>
     SOME (taken::l)
    | NONE => NONE)
  | _ => NONE
 )
Termination
WF_REL_TAC `measure LENGTH` >>
rpt strip_tac >>
imp_res_tac oTAKE_DROP_SOME >>
imp_res_tac oDROP_LENGTH >>
gs[]
End
   
Definition v2w16s''_def:
 (v2w16s'' v = if (LENGTH v) MOD 16 = 0 then (v2w16s''' v) else NONE)
End

Definition get_checksum_incr''_def:
 (get_checksum_incr'' scope_list ext_data_name =
   (case lookup_lval' scope_list ext_data_name of
    | SOME (v_bit (bl, n)) =>
     if n MOD 16 = 0 then (v2w16s''' bl) else NONE
    | SOME (v_header vbit f_list) =>
     (case header_entries2v (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | SOME (v_struct f_list) =>
     (case header_entries2v (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | _ => NONE)
 )
End

(* Note that this assumes the order of fields in the header is correct *)
Definition Checksum16_update_def:
 (Checksum16_update ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     (case get_checksum_incr'' scope_list (lval_varname (varn_name "data")) of
      | SOME checksum_incr =>
       SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum (ipv4_checksum ++ checksum_incr))), v_map, ctrl), scope_list, status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(*******)
(* get *)

(* TODO: carry_in hard-coded as false *)
(* TODO: This is the bitvector version of the function on words *)
Definition add_with_carry'_def:
 add_with_carry' (x,y) =
  let
   unsigned_sum = v2n x + v2n y;
   result = fixwidth 16 $ n2v unsigned_sum;
   carry_out = (v2n result <> unsigned_sum) and
   overflow =
     ((HD x <=> HD y) /\ (HD x <=/=> HD result))
  in
   (result,carry_out,overflow)
End

(* TODO: This is the bitvector version of the function on words *)
Definition add_ones_complement'_def:
 add_ones_complement' (x, y) =
  let
   (result,carry_out,overflow) = add_with_carry' (x, y)
  in
   if carry_out
   then fixwidth 16 $ n2v (v2n result + 1)
   else result
End

Definition sub_ones_complement'_def:
 sub_ones_complement' (x, y) =
  let
   (result,carry_out,overflow) = add_with_carry' (x, MAP $~ y)
  in
   if carry_out
   then fixwidth 16 $ n2v (v2n result + 1)
   else MAP $~ result
End

Definition compute_checksum16_inner_def:
 (compute_checksum16_inner ([]:(bool list) list) = (fixwidth 16 $ n2v 0)) /\
 (compute_checksum16_inner ((h::t):(bool list) list) =
  add_ones_complement' (h, compute_checksum16_inner (t:(bool list) list))
 )
End

Definition all_lists_length_16_def:
 (all_lists_length_16 ([]:(bool list) list) = T) /\
 (all_lists_length_16 (h::t) = 
   if LENGTH h = 16
   then all_lists_length_16 t
   else F)
End

Definition compute_checksum16_def:
 compute_checksum16 ipv4_checksum =
  if all_lists_length_16 ipv4_checksum
  then
   SOME $ MAP $~ $ compute_checksum16_inner ipv4_checksum
  else NONE
End

Definition ALOOKUP_compute_checksum16_def:
 ALOOKUP_compute_checksum16 alist el =
  case ALOOKUP alist el of
   | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
    compute_checksum16 ipv4_checksum
   | _ => NONE
End

Definition Checksum16_get_def:
 (Checksum16_get ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP_compute_checksum16 ext_obj_map i of
    | SOME ipv4_checksum' =>
     SOME ((counter, ext_obj_map, v_map, ctrl):vss_ascope, scope_list, status_returnv (v_bit (ipv4_checksum', 16)))
    | _ => NONE)
  | _ => NONE
 )
End


(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(*
Definition get_optional_bits:
 get_optional_bits header = ((v2n (TAKE 4 (DROP 116 header)))*32) - 160
End
*)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition vss_input_f_def:
 (vss_input_f tau_uninit_v (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [("b", v_ext_ref counter); ("b_temp", v_ext_ref (counter+1));
                                    ("parsedHeaders", tau_uninit_v);
                                    ("inCtrl", v_struct [("inputPort", v_bit (fixwidth 4 (n2v p), 4)  )]);
                                    (* TODO: What should be the default value here? Is this undefined? *)
                                    ("outCtrl", v_struct [("outputPort", v_bit (fixwidth 4 (n2v p), 4) )]);
                                    ("parseError", v_bit (fixwidth 32 (n2v 0), 32))] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):vss_ascope))
End

(* TODO: Make general in p4_core *)
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
  (case ALOOKUP v_map "b" of
   | SOME (v_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map "b_temp" of
       | SOME (v_ext_ref i') =>
        (case ALOOKUP v_map "parsedHeaders" of
         | SOME (v_struct hdrs) =>
          let v_map' = AUPDATE v_map ("headers", v_struct hdrs) in
          let ext_obj_map' = AUPDATE ext_obj_map (i, INL (core_v_ext_packet [])) in
          let ext_obj_map'' = AUPDATE ext_obj_map' (i', INL (core_v_ext_packet bl)) in
           SOME (counter, ext_obj_map'', v_map', ctrl)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
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

(* TODO: Outsource obtaining the output port to an external function? *)
Definition vss_output_f_def:
 vss_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  (case vss_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet headers)) =>
    (case vss_lookup_obj ext_obj_map v_map "b_temp" of
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

Definition ctrl_check_ttl_def:
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
