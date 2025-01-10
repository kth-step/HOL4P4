open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_cake_import";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

(* This file contains facilities to import HOL4P4 programs from their regular representation to
 * a CakeML-friendly representation *)

(*********************)
(* Core architecture *)

(* Gather extern function implementations, which may contain hard-coded variable names *)
val core_implementations =
 [verify_gen_def, header_is_valid_def, header_set_valid_def, header_set_invalid_def,
  packet_in_extract_gen_def, packet_in_lookahead_gen_def, packet_in_advance_gen_def,
  packet_out_emit_gen_def]

(* Filter out identical terms while keeping their order *)
local
 fun filter_equal_terms' []     filtered_list = filtered_list
  | filter_equal_terms' (h::t) [] = filter_equal_terms' t [h]
  | filter_equal_terms' (h::t) filtered_list =
   if isSome (List.find (term_eq h) filtered_list)
   then filter_equal_terms' t filtered_list
   else filter_equal_terms' t (h::filtered_list)
in
fun filter_equal_terms tm_list = rev $ filter_equal_terms' tm_list []
end
;

fun get_varn_name_strings impls =
 let
  val impl_tms = map (rhs o snd o strip_forall o concl) impls
  val varn_names = foldl (fn (tm, l) => l@(find_terms (fn t => is_varn_name t) tm)) [] impl_tms
 in
  map dest_varn_name $ filter_equal_terms varn_names
 end
;

val core_impl_varnames = get_varn_name_strings core_implementations

local
fun add_to_dict' []     dict _     = dict
  | add_to_dict' (h::t) dict i =
 let
  val word = wordsSyntax.mk_wordii (i, 64)
 in
    case Redblackmap.peek (dict, h) of
     SOME v => add_to_dict' t dict i
   | NONE => add_to_dict' t (Redblackmap.insert (dict, h, word)) (i+1)
 end  
in
fun add_to_dict additions dict =
 let
  val size = Redblackmap.numItems dict
 in
  add_to_dict' additions dict size
 end
end

val varnames_of_vmap = map (fst o pairSyntax.dest_pair) o (fst o listSyntax.dest_list)

val core_impl_dict =
 add_to_dict core_impl_varnames (Redblackmap.mkDict (fn (a,b) => String.compare (stringSyntax.fromHOLstring a, stringSyntax.fromHOLstring b))):(term, term) Redblackmap.dict;
(*
Redblackmap.listItems core_impl_dict
*)

(** Some new architectural functions **)

Definition v_map_to_scope'_def:
 (v_map_to_scope' [] = []) /\
 (v_map_to_scope' (((k, v)::t):(word64, v) alist) =
  ((varn'_name k, (v, NONE:lval' option))::v_map_to_scope' t)
 )
End

Definition scope_to_vmap'_def:
 (scope_to_vmap' [] = SOME []) /\
 (scope_to_vmap' ((vn, (v:v, lval_opt:lval' option))::t) =
  case vn of
   | (varn'_name k) => oCONS ((k, v), scope_to_vmap' t)
   | _ => NONE
 )
End

Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope' v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End


(***********)
(* V1Model *)

Type v1model_ascope' = “:(num # ((num, v1model_sum_v_ext) alist) # ((word64, v) alist) # v1model_ctrl)”;

Definition v1model_ascope_lookup'_def:
 v1model_ascope_lookup (ascope:v1model_ascope') ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition v1model_ascope_update'_def:
 v1model_ascope_update' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition v1model_ascope_update_v_map'_def:
 v1model_ascope_update_v_map' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition v1model_packet_in_extract'_def:
 v1model_packet_in_extract' = packet_in_extract_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_in_lookahead'_def:
 v1model_packet_in_lookahead' = packet_in_lookahead_gen v1model_ascope_lookup v1model_ascope_update_v_map
End

Definition v1model_packet_in_advance'_def:
 v1model_packet_in_advance' = packet_in_advance_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_out_emit'_def:
 v1model_packet_out_emit' = packet_out_emit_gen v1model_ascope_lookup v1model_ascope_update
End

Definition v1model_ascope_read_ext_obj'_def:
 v1model_ascope_read_ext_obj' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') vname =
  case ALOOKUP v_map vname of
  | SOME (v_ext_ref n) =>
   ALOOKUP ext_obj_map n
  | _ => NONE
End

Definition v1model_ascope_of_conc_state'_def:
 v1model_ascope_of_conc_state' (io1,io2,(ascope:v1model_ascope')) =
  ascope
End

(* Some specific stuff left out for now *)
val v1model_implementations =
 [v1model_mark_to_drop_def, v1model_assert_def, v1model_assume_def,
  v1model_direct_counter_construct_def, v1model_direct_counter_count_def,
  v1model_verify_checksum_def, v1model_update_checksum_def, register_construct_def,
  register_read_def, register_write_def]

(* Architectural functions mentioning variables by hard-coded names *)
val v1model_archfuns = [v1model_postparser_def]

val v1model_varnames = get_varn_name_strings (v1model_implementations@v1model_archfuns)

val v1model_init_vmapnames = varnames_of_vmap p4_v1modelLib.v1model_init_v_map

(* TODO: just copy-pasted from V1Model Script file, put in V1Model Lib *)
val v_map_varnames =
 [“"b"”, “"b_temp"”, “"standard_metadata"”, “"parsedHdr"”, “"hdr"”, “"meta"”]
;

val v1model_dict =
 add_to_dict (v1model_init_vmapnames@v_map_varnames@v1model_varnames) core_impl_dict;
(*
Redblackmap.listItems v1model_dict
*)

Definition v1model_postparser'_def:
 v1model_postparser' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  (case ALOOKUP v_map 8w of
   | SOME (v_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map 9w of
       | SOME (v_ext_ref i') =>
        (case ALOOKUP v_map 11w of
         | SOME v =>
          let v_map' = p4$AUPDATE v_map (12w, v) in
           (case ALOOKUP v_map 7w of
            | SOME v' =>
             (case assign' [v_map_to_scope' v_map'] v' (lval'_field (lval'_varname (varn'_name 10w)) "parser_error") of
              | SOME [v_map_scope] =>
               (case scope_to_vmap' v_map_scope of
                | SOME v_map'' =>
                 let v_map''' = p4$AUPDATE v_map'' (7w, v_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl') = (v1model_ascope_update' (counter, ext_obj_map, v_map''', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (v1model_ascope_update' (counter', ext_obj_map', v_map'''', ctrl') i (INL (core_v_ext_packet [])))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

fun mk_v_bitii' (num, width) =
 let
  val width_tm = term_of_int width
 in
  mk_v_bit $ mk_pair (mk_fixwidth (width_tm, mk_n2v $ term_of_int num), width_tm)
 end
;
val v1model_standard_metadata_zeroed' =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(“"ingress_port"”, mk_v_bitii' (0, 9)),
    (“"egress_spec"”, mk_v_bitii' (0, 9)),
    (“"egress_port"”, mk_v_bitii' (0, 9)),
    (“"instance_type"”, mk_v_bitii' (0, 32)),
    (“"packet_length"”, mk_v_bitii' (0, 32)),
    (“"enq_timestamp"”, mk_v_bitii' (0, 32)),
    (“"enq_qdepth"”, mk_v_bitii' (0, 19)),
    (“"deq_timedelta"”, mk_v_bitii' (0, 32)),
    (“"deq_qdepth"”, mk_v_bitii' (0, 19)),
    (“"ingress_global_timestamp"”, mk_v_bitii' (0, 48)),
    (“"egress_global_timestamp"”, mk_v_bitii' (0, 48)),
    (“"mcast_grp"”, mk_v_bitii' (0, 16)),
    (“"egress_rid"”, mk_v_bitii' (0, 16)),
    (“"checksum_error"”, mk_v_bitii' (0, 1)),
    (“"parser_error"”, mk_v_bitii' (0, 32)),
    (“"priority"”, mk_v_bitii' (0, 3))],
   “:(string # p4$v)”);
(*
Redblackmap.find (v1model_dict, “"meta"”)
*)
Definition v1model_input_f'_def:
 (v1model_input_f' (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   (* let counter' = ^v1model_init_counter in *)
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [(8w, v_ext_ref counter);
                                    (9w, v_ext_ref (counter+1));
                                    (10w, v_struct (p4$AUPDATE (^v1model_standard_metadata_zeroed') ("ingress_port", (v_bit (fixwidth 9 $ n2v p, 9) ) )));
                                    (11w, tau1_uninit_v);
                                    (12w, tau1_uninit_v);
                                    (13w, tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope'))
End

Definition v1model_reduce_nonout'_def:
 (v1model_reduce_nonout' ([], elist:e' list, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout' (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout' (dlist, elist, v_map))
  else
   (case e of
    | (e'_var (varn'_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e'_v v, v1model_reduce_nonout' (dlist, elist, v_map))
       else oCONS (e'_v (init_out_v_cake v), v1model_reduce_nonout' (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout' (_, _, v_map) = NONE)
End


(* Uses the above and copyin' *)
Definition v1model_copyin_pbl'_def:
 v1model_copyin_pbl' (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  case v1model_reduce_nonout' (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin' xlist dlist elist' [v_map_to_scope' v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End
(*
(* Uses update_return_frame' *)
Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope' v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End
*)
(* Uses the above *)
Definition v1model_copyout_pbl'_def:
 v1model_copyout_pbl' (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope', dlist, xlist, (status:status)) =
  case copyout_pbl_gen' xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap' v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):v1model_ascope')
    | NONE => NONE)
  | _ => NONE
End                 

val _ = export_theory ();
