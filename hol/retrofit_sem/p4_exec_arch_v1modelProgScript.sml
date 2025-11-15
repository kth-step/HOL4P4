open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_arch_v1modelProg";

open p4Theory p4_auxTheory p4_coreTheory p4_v1modelTheory;
open p4_exec_archTheory p4_exec_arch_v1modelTheory;
open p4_exec_semTheory;
open p4_exec_semProgTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "p4_exec_semProg";

val _ = ml_prog_update (open_module "p4_exec_arch_v1modelProg");

(** V1Model arch implementation **)

(* Architectural functions: *)

val _ = translate v_map_to_scope_def;
val _ = translate oCONS_def;
val _ = translate scope_to_vmap_def;
val _ = translate v1model_ascope_update_def;

val _ = translate v1model_postparser_def;
val _ = translate v1model_preingress_def;

val _ = translate v1model_input_f_def;

val _ = translate v1model_is_drop_port_def;
val _ = translate v1model_lookup_obj_def;

val _ = translate v1model_output_f_def;

val _ = translate init_out_v_cake_def;
val _ = translate v1model_reduce_nonout_def;
val _ = translate v1model_copyin_pbl_def;
Theorem v1model_copyin_pbl_side_thm:
!xlist dlist elist counter ext_obj_map v_map ctrl.
v1model_copyin_pbl_side (xlist,dlist,elist,counter,ext_obj_map,v_map,ctrl)
Proof
simp[Once $ definition "v1model_copyin_pbl_side_def", copyin_exec_side_thm]
QED
val _ = update_precondition v1model_copyin_pbl_side_thm;

val _ = translate copyout_pbl_gen_def;
val _ = translate v1model_copyout_pbl_def;

val _ = translate FOLDL_MATCH_alt_def;
val _ = translate FOLDL_MATCH_def;
val _ = translate listTheory.LIST_TO_SET_DEF;
val _ = translate boolTheory.IN_DEF;
val _ = translate v1model_apply_table_f''_def;

(* Extern implementations: *)

val _ = translate v1model_mark_to_drop_def;

val _ = translate v1model_ascope_update_v_map_def;
val _ = translate verify_gen_def;
val _ = translate v1model_verify_def;

val _ = translate v1model_assert_def;

val _ = translate v1model_assume_def;

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

val _ = translate v1model_direct_counter_construct_def;
val _ = translate v1model_direct_counter_count_def;

val _ = translate v1model_direct_meter_construct_def;

val _ = translate v1model_action_selector_construct_def;

(* TODO: The below is defined in terms of functions that uses ARB... *)
(*
val _ = translate v1model_register_construct_inner_def;
val _ = translate register_construct_def;

val _ = translate v1model_register_read_inner_def;
val _ = translate register_read'_def;

val _ = translate v1model_register_write_inner_def;
val _ = translate register_write'_def;
*)

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
