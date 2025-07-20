open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_arch_v1modelProg";

open p4Theory p4_auxTheory p4_coreTheory p4_v1modelTheory;
open p4_cake_auxTheory p4_cake_archTheory p4_cake_arch_v1modelTheory;
open p4_cake_auxLib;
open p4_cake_exec_semTheory;
open p4_cake_exec_semProgTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "p4_cake_exec_semProg";

val _ = ml_prog_update (open_module "p4_cake_arch_v1modelProg");

(** V1Model arch implementation **)

(* Architectural functions: *)

val _ = translate v_map_to_scope'_def;
val _ = translate oCONS_def;
val _ = translate scope_to_vmap'_def;
val _ = translate v1model_ascope_update'_def;
val _ = translate v1model_postparser'_def;
val _ = translate v1model_preingress'_def;

val _ = translate v1model_input_f'_def;

val _ = translate v1model_is_drop_port_def;
val _ = translate v1model_lookup_obj'_def;
val _ = translate v1model_output_f'_def;

val _ = translate v1model_reduce_nonout'_def;
val _ = translate v1model_copyin_pbl'_def;

val _ = translate copyout_pbl_gen'_def;
val _ = translate v1model_copyout_pbl'_def;

(* Table matching *)
val _ = translate listTheory.LIST_TO_SET_DEF;
val _ = translate boolTheory.IN_DEF;

val _ =
 if matching_optimization
 then
  let
   val _ = translate match_all_e_alt''_def;
   val _ = translate FOLDL_MATCH_alt''_def;
   val _ = translate FOLDL_MATCH''_def;
   val _ = translate e_list_to_word64s_list_def;
   val _ = translate v1model_apply_table_f''_def;
  in
   ()
  end
 else
  let
   val _ = translate match_all'_def;
   val _ = translate FOLDL_MATCH_alt'_def;
   val _ = translate FOLDL_MATCH'_def;
   val _ = translate v1model_apply_table_f'_def;
  in
   ()
  end
;

(* Extern implementations: *)

val _ = translate v1model_mark_to_drop'_def;

val _ = translate v1model_ascope_update_v_map'_def;
val _ = translate verify_gen'_def;
val _ = translate v1model_verify'_def;

val _ = translate v1model_assert'_def;

val _ = translate v1model_assume'_def;

val _ = translate v1model_verify_checksum'_def;

val _ = translate v1model_update_checksum'_def;

val _ = translate lookup_lval_header'_def;
val _ = translate lookup_ascope_gen_def;
val _ = translate size_in_bits'_def;
val _ = translate set_bool'_def;
val _ = translate set_bit'_def;
val _ = translate set_fields'_def;
val _ = translate set_header'_def;
val _ = translate update_ascope_gen_def;

val _ = translate w8_to_v_def;
val _ = translate byte_list_to_bool_list_take_def;
val _ = translate packet_in_extract_gen'_def;
val _ = translate v1model_ascope_lookup'_def;
val _ = translate v1model_packet_in_extract'_def;

val _ = translate set_struct'_def;
val _ = translate set_v'_def;
val _ = translate packet_in_lookahead_gen'_def;
val _ = translate v1model_packet_in_lookahead'_def;

val _ = translate lookup_lval_bit32'_def;
val _ = translate packet_in_advance_gen'_def;
val _ = translate v1model_packet_in_advance'_def;

val _ = translate flatten_v_l'_def;
val _ = translate v2w8_def;
val _ = translate bool_list_to_byte_list_def;
val _ = translate packet_out_emit_gen'_def;
val _ = translate v1model_packet_out_emit'_def;

val _ = translate v1model_direct_counter_construct'_def;
val _ = translate v1model_direct_counter_count'_def;

val _ = translate v1model_direct_meter_construct'_def;

val _ = translate v1model_action_selector_construct'_def;

(* TODO: The below is defined in terms of functions that uses ARB... *)
(*
val _ = translate v1model_register_construct_inner_def;
val _ = translate register_construct_def;

val _ = translate v1model_register_read_inner_def;
val _ = translate register_read'_def;
*)

val _ = translate v1model_register_write_inner_def;
val _ = translate register_write'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
