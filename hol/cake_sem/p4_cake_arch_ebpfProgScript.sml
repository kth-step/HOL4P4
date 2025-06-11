open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_arch_ebpfProg";

open p4Theory p4_auxTheory p4_coreTheory p4_ebpfTheory;
open p4_cake_auxTheory p4_cake_archTheory p4_cake_arch_ebpfTheory;
open p4_cake_exec_semTheory;
open p4_cake_exec_semProgTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "p4_cake_exec_semProg";

val _ = ml_prog_update (open_module "p4_cake_arch_ebpfProg");

(** eBPF arch implementation **)

(* Architectural functions: *)

val _ = translate v_map_to_scope'_def;
val _ = translate oCONS_def;
val _ = translate scope_to_vmap'_def;

val _ = translate ebpf_ascope_lookup'_def;
val _ = translate ebpf_ascope_update'_def;
val _ = translate ebpf_ascope_update_v_map'_def;

val _ = translate lookup_lval_header'_def;
val _ = translate (EVAL “w2v (w:word8)” |> SIMP_RULE (srw_ss()) [word_bit_test,word_bit_def,word_bit]);
val _ = translate w8_to_v_def;
val _ = translate byte_list_to_bool_list_take_def;
val _ = translate lookup_ascope_gen_def;
val _ = translate size_in_bits'_def;
val _ = translate set_bool'_def;
val _ = translate set_bit'_def;
val _ = translate set_fields'_def;
val _ = translate set_header'_def;
val _ = translate update_ascope_gen_def;
val _ = translate packet_in_extract_gen'_def;
val _ = translate ebpf_packet_in_extract'_def;

val _ = translate set_struct'_def;
val _ = translate set_v'_def;
val _ = translate packet_in_lookahead_gen'_def;
val _ = translate ebpf_packet_in_lookahead'_def;

val _ = translate lookup_lval_bit32'_def;
val _ = translate packet_in_advance_gen'_def;
val _ = translate ebpf_packet_in_advance'_def;

val _ = translate flatten_v_l'_def;
val _ = translate v2w8_def;
val _ = translate bool_list_to_byte_list_def;
val _ = translate packet_out_emit_gen'_def;
val _ = translate ebpf_packet_out_emit'_def;

val _ = translate verify_gen'_def;
val _ = translate ebpf_verify'_def;

(* Extern implementations *)

val _ = translate CounterArray_construct'_def;

val _ = translate CounterArray_increment'_def;

val _ = translate CounterArray_add'_def;

(* Misc. arch functions *)

val _ = translate ebpf_input_f'_def;

val _ = translate ebpf_reduce_nonout'_def;

val _ = translate ebpf_copyin_pbl'_def;

val _ = translate ebpf_lookup_obj'_def;
val _ = translate ebpf_inputPort_to_num'_def;
val _ = translate ebpf_output_f'_def;

val _ = translate FOLDL_MATCH_def;
val _ = translate ebpf_apply_table_f'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
