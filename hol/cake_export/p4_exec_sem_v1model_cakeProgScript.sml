open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_v1model_cakeProg";

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;
open p4_coreTheory p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_arch_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

(* V1Model architecture functions *)

(* Uses assign' *)
Definition v1model_postparser'_def:
 v1model_postparser' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case ALOOKUP v_map "b" of
   | SOME (v_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map "b_temp" of
       | SOME (v_ext_ref i') =>
        (case ALOOKUP v_map "parsedHdr" of
         | SOME v =>
          let v_map' = p4$AUPDATE v_map ("hdr", v) in
           (case ALOOKUP v_map "parseError" of
            | SOME v' =>
             (case assign' [v_map_to_scope v_map'] v' (lval_field (lval_varname (varn_name "standard_metadata")) "parser_error") of
              | SOME [v_map_scope] =>
               (case scope_to_vmap v_map_scope of
                | SOME v_map'' =>
                 let v_map''' = p4$AUPDATE v_map'' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl') = (v1model_ascope_update (counter, ext_obj_map, v_map''', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (v1model_ascope_update (counter', ext_obj_map', v_map'''', ctrl') i (INL (core_v_ext_packet [])))
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

(* Avoids some word stuff *)
Definition v1model_input_f'_def:
 (v1model_input_f' (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   (* let counter' = ^v1model_init_counter in *)
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [("b", v_ext_ref counter);
                                    ("b_temp", v_ext_ref (counter+1));
                                    ("standard_metadata", v_struct (p4$AUPDATE (^v1model_standard_metadata_zeroed') ("ingress_port", (v_bit (fixwidth 9 $ n2v p, 9) ) )));
                                    ("parsedHdr", tau1_uninit_v);
                                    ("hdr", tau1_uninit_v);
                                    ("meta", tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope))
End

(* init_out_v_cake is used for unknown values *)
Definition v1model_reduce_nonout'_def:
 (v1model_reduce_nonout' ([], elist, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout' (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout' (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, v1model_reduce_nonout' (dlist, elist, v_map))
       else oCONS (e_v (init_out_v_cake v), v1model_reduce_nonout' (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout' (_, _, v_map) = NONE)
End

(* Uses the above and copyin' *)
Definition v1model_copyin_pbl'_def:
 v1model_copyin_pbl' (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case v1model_reduce_nonout' (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin' xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End

(* Uses update_return_frame' *)
Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End

(* Uses the above *)
Definition v1model_copyout_pbl'_def:
 v1model_copyout_pbl' (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen' xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):v1model_ascope)
    | NONE => NONE)
  | _ => NONE
End

val _ = translation_extends "p4_exec_sem_arch_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_v1model_cake");

(* Architectural functions: *)

val _ = translate v_map_to_scope_def;
val _ = translate oCONS_def;
val _ = translate scope_to_vmap_def;
val _ = translate v1model_ascope_update_def;
val _ = translate v1model_postparser'_def;

val _ = translate v1model_input_f'_def;

val _ = translate v1model_is_drop_port_def;
val _ = translate v1model_lookup_obj_def;
val _ = translate v1model_output_f_def;

val _ = translate v1model_reduce_nonout'_def;
val _ = translate v1model_copyin_pbl'_def;

val _ = translate copyout_pbl_gen'_def;
val _ = translate v1model_copyout_pbl'_def;

val _ = translate FOLDL_MATCH_alt_def;
val _ = translate FOLDL_MATCH_def;
val _ = translate listTheory.LIST_TO_SET_DEF;
val _ = translate boolTheory.IN_DEF;
val _ = translate v1model_apply_table_f_def;

(* Extern implementations: *)

val _ = translate v1model_mark_to_drop_def;

val _ = translate v1model_ascope_update_v_map_def;
val _ = translate verify_gen_def;
val _ = translate v1model_verify_def;

val _ = translate v1model_verify_checksum_def;

val _ = translate v1model_update_checksum_def;

val _ = translate lookup_lval_header_def;
val _ = translate lookup_ascope_gen_def;
val _ = translate size_in_bits_def;
val _ = translate set_bool_def;
val _ = translate set_bit_def;
val _ = translate set_fields_def;
val _ = translate set_header_def;
val _ = translate update_ascope_gen_def;
val _ = translate packet_in_extract_gen_def;
val _ = translate v1model_ascope_lookup_def;
val _ = translate v1model_packet_in_extract_def;

val _ = translate set_struct_def;
val _ = translate set_v_def;
val _ = translate packet_in_lookahead_gen_def;
val _ = translate v1model_packet_in_lookahead_def;

val _ = translate lookup_lval_bit32_def;
val _ = translate packet_in_advance_gen_def;
val _ = translate v1model_packet_in_advance_def;

val _ = translate flatten_v_l_def;
val _ = translate packet_out_emit_gen_def;
val _ = translate v1model_packet_out_emit_def;

(* TODO: The below is defined in terms of functions that uses ARB... *)
(*
val _ = translate v1model_register_construct_inner_def;
val _ = translate register_construct_def;

val _ = translate v1model_register_read_inner_def;
val _ = translate register_read_def;
*)

val _ = translate v1model_register_write_inner_def;
val _ = translate register_write_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
