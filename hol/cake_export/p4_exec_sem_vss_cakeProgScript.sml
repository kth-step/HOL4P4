open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_vss_cakeProg";

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;
open p4_coreTheory p4_vssTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_arch_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

(* VSS architecture functions *)

Definition vss_reduce_nonout'_def:
 (vss_reduce_nonout' ([], elist, v_map) =
  SOME []
 ) /\
 (vss_reduce_nonout' (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, vss_reduce_nonout' (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, vss_reduce_nonout' (dlist, elist, v_map))
       else oCONS (e_v (init_out_v_cake v), vss_reduce_nonout' (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (vss_reduce_nonout' (_, _, v_map) = NONE)
End

Definition vss_copyin_pbl'_def:
 vss_copyin_pbl' (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):vss_ascope) =
  case vss_reduce_nonout' (dlist, elist, v_map) of
  | SOME elist' =>
   copyin' xlist dlist elist' [v_map_to_scope v_map] [ [] ]
  | NONE => NONE
End

(* TODO: Generic. Upstream to regular arch scripts? *)
Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End

Definition vss_copyout_pbl'_def:
 vss_copyout_pbl' (g_scope_list, (counter, ext_obj_map, v_map, ctrl):vss_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen' xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):vss_ascope)
    | NONE => NONE)
  | _ => NONE
End

Definition vss_packet_in_extract_gen_def:
 (vss_packet_in_extract_gen ascope_lookup (ascope_update:num #
    (num # (core_v_ext + vss_v_ext)) list #
    (string # p4$v) list #
    (string # (((e list -> bool) # num) # string # e list) list) list ->
    num ->
    core_v_ext + vss_v_ext ->
    num #
    (num # (core_v_ext + vss_v_ext)) list #
    (string # p4$v) list #
    (string # (((e list -> bool) # num) # string # e list) list) list) ascope_update_v_map (ascope:vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_header scope_list (lval_varname (varn_name "headerLvalue")) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, vss_v_ext) sum) =>
       (case size_in_bits (v_header valid_bit x_v_l) of
        | SOME size' =>
         if arithmetic$<= size' (LENGTH packet_in_bl)
         then
          (case set_header x_v_l packet_in_bl of
           | SOME header =>
            (case assign' scope_list header (lval_varname (varn_name "headerLvalue")) of
             | SOME scope_list' =>
              SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP size' packet_in_bl))):(core_v_ext, vss_v_ext) sum), scope_list', status_returnv v_bot)
             | NONE => NONE)
           | NONE => NONE)
         else
          (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet [])):(core_v_ext, vss_v_ext) sum)) "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject")
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

(* TODO: Why do we need to fix the packet_in_extract stuff? *)
Definition vss_packet_in_extract'_def:
 vss_packet_in_extract':((num #
  (num # (core_v_ext + vss_v_ext)) list #
  (string # p4$v) list #
  (string # (((e list -> bool) # num) # string # e list) list) list) #
 (varn # p4$v # lval option) list list #
 (varn # p4$v # lval option) list list ->
 ((num #
   (num # (core_v_ext + vss_v_ext)) list #
   (string # p4$v) list #
   (string # (((e list -> bool) # num) # string # e list) list) list) #
  (varn # p4$v # lval option) list list # status) option) = vss_packet_in_extract_gen vss_ascope_lookup vss_ascope_update vss_ascope_update_v_map
End

Definition Checksum16_construct'_def:
 (Checksum16_construct' ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (vss_v_ext_ipv4_checksum ([]:(bool list) list))) in
  (case assign' scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
   | SOME scope_list' =>
    SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
   | NONE => NONE)
 )
End

Definition Checksum16_clear'_def:
 (Checksum16_clear' ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum ([]:(bool list) list))), v_map, ctrl), scope_list, status_returnv v_bot)
  | _ => NONE
 )
End

Definition Checksum16_update'_def:
 (Checksum16_update' ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
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

(* TODO: Upstream this and the below two? *)
Definition compute_checksum16'_def:
 (compute_checksum16' ([]:(bool list) list) = (fixwidth 16 $ n2v 0)) /\
 (compute_checksum16' ((h::t):(bool list) list) =
  add_ones_complement' (h, compute_checksum16' (t:(bool list) list))
 )
End
(* TODO: Better name *)
Definition ALOOKUP'_inner_def:
 ALOOKUP'_inner ipv4_checksum =
    if all_lists_length_16 ipv4_checksum
    then
     SOME $ MAP $~ $ compute_checksum16' ipv4_checksum
    else NONE
End
(* TODO: Better name *)
Definition ALOOKUP'_def:
 ALOOKUP' alist el =
  case ALOOKUP alist el of
   | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
    ALOOKUP'_inner ipv4_checksum
   | _ => NONE
End

Definition Checksum16_get'_def:
 (Checksum16_get' ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval' scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP' ext_obj_map i of
    | SOME ipv4_checksum' =>
     SOME ((counter, ext_obj_map, v_map, ctrl):vss_ascope, scope_list, status_returnv (v_bit (ipv4_checksum', 16)))
    | _ => NONE)
  | _ => NONE
 )
End

(* TODO: Move to p4_exec_sem_arch_cakeProg, since it's not architecture-specific *)
(* TODO: Note that this does not distinguish failing from finishing *)
Definition arch_multi_exec'_def:
 (arch_multi_exec' actx ((aenv, g_scope_list, arch_frame_list, status):'a astate) 0 =
  SOME (aenv, g_scope_list, arch_frame_list, status))
  /\
 (arch_multi_exec' actx (aenv, g_scope_list, arch_frame_list, status) (SUC fuel) =
  case arch_exec' actx (aenv, g_scope_list, arch_frame_list, status) of
  | SOME (aenv', g_scope_list', arch_frame_list', status') =>
   arch_multi_exec' actx (aenv', g_scope_list', arch_frame_list', status') fuel
  | NONE => SOME (aenv, g_scope_list, arch_frame_list, status))
End

Definition p4_get_output_list_def:
 p4_get_output_list (((i, io_list, io_list', ascope), g_scope_list, arch_frame_list, status):'a astate) =
  io_list'
End

fun mk_v_bitii' (num, width) =
 let
  val width_tm = numSyntax.term_of_int width
 in
  mk_v_bit $ pairSyntax.mk_pair (bitstringSyntax.mk_fixwidth (width_tm, bitstringSyntax.mk_n2v $ numSyntax.term_of_int num), width_tm)
 end
;

(*
(* TODO: Hack, some type mismatch when using regular syntax functions *)
val (v_header_tm, mk_v_header, dest_v_header, is_v_header) =
  syntax_fns2 "p4" "v_header";
fun mk_v_header_list vbit x_v_l =
  mk_v_header (vbit, (listSyntax.mk_list ((map (fn (a, b) => mk_pair (a, b)) x_v_l), ``:(string # p4$v) ``)));
val (v_struct_tm, mk_v_struct, dest_v_struct, is_v_struct) =
  syntax_fns1 "p4" "v_struct";
fun mk_v_struct_list x_v_l =
  mk_v_struct (listSyntax.mk_list ((map (fn (a, b) => mk_pair (a, b)) x_v_l), ``:(string # p4$v)``));

val ipv4_header_uninit =
 mk_v_header_list F 
                  [(``"version"``, mk_v_bitii' (0, 4)),
                   (``"ihl"``, mk_v_bitii' (0, 4)),
                   (``"diffserv"``, mk_v_bitii' (0, 8)),
                   (``"totalLen"``, mk_v_bitii' (0, 16)),
                   (``"identification"``, mk_v_bitii' (0, 16)),
                   (``"flags"``, mk_v_bitii' (0, 3)),
                   (``"fragOffset"``, mk_v_bitii' (0, 13)),
                   (``"ttl"``, mk_v_bitii' (0, 8)),
                   (``"protocol"``, mk_v_bitii' (0, 8)),
                   (``"hdrChecksum"``, mk_v_bitii' (0, 16)),
                   (``"srcAddr"``, mk_v_bitii' (0, 32)),
                   (``"dstAddr"``, mk_v_bitii' (0, 32))];
val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_bitii' (0, 48)),
                   (``"srcAddr"``, mk_v_bitii' (0, 48)),
                   (``"etherType"``, mk_v_bitii' (0, 16))];
val vss_parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];
*)


val _ = translation_extends "p4_exec_sem_arch_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_vss_cake");

val _ = translate arch_multi_exec'_def;

val _ = translate vss_parser_runtime_def;

val _ = translate vss_input_f_def;

val _ = translate vss_lookup_obj_def;
val _ = translate vss_output_f_def;

val _ = translate v_map_to_scope_def;
val _ = translate oCONS_def;
val _ = translate vss_reduce_nonout'_def;
val _ = translate vss_copyin_pbl'_def;

val _ = translate scope_to_vmap_def;
val _ = translate copyout_pbl_gen'_def;
val _ = translate vss_copyout_pbl'_def;

val _ = translate FOLDL_MATCH_def;
val _ = translate ctrl_check_ttl_def;
val _ = translate vss_apply_table_f_def;

val _ = translate header_is_valid_def;

val _ = translate header_set_valid_def;

val _ = translate header_set_invalid_def;

val _ = translate vss_ascope_update_v_map_def;
val _ = translate verify_gen_def;
val _ = translate vss_verify;

val _ = translate Checksum16_construct'_def;

val _ = translate Checksum16_clear'_def;

val _ = translate oTAKE_DROP_def;
val _ = translate v2w16s'''_def;
val _ = translate header_entries2v_def;
val _ = translate v2w16s''_def;
val _ = translate get_checksum_incr''_def;
val _ = translate Checksum16_update'_def;

val _ = translate add_with_carry'_def;
val _ = translate add_ones_complement'_def;
val _ = translate compute_checksum16'_def;
val _ = translate all_lists_length_16_def;
val _ = translate ALOOKUP'_inner_def;
(* TODO: Clean up proof *)
Theorem alookup'_inner_side:
!v1. alookup'_inner_side v1
Proof
simp[Once $ definition "alookup'_inner_side_def"] \\
Induct >- (
 simp[Once $ theorem "compute_checksum16'_side_def", all_lists_length_16_def]
) \\
rpt strip_tac \\
gs[all_lists_length_16_def] \\
gs[Once $ theorem "compute_checksum16'_side_def"] \\
Cases_on ‘v1’ >- (
 simp[theorem "compute_checksum16'_side_def"] \\
 gs[compute_checksum16'_def, Once $ definition "add_ones_complement'_side_def",
    Once $ definition "add_with_carry'_side_def"] \\
 rpt strip_tac >- (
  gs[]
 ) >- (
  gs[bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
 ) >- (
  gs[]
 ) \\
 gs[bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
) \\
qpat_x_assum ‘!x2 x1. _’ (fn thm => ASSUME_TAC $ Q.SPECL [‘h'’, ‘t’] thm) \\
simp[Once $ theorem "compute_checksum16'_side_def", all_lists_length_16_def] \\
simp[Once $ definition "add_ones_complement'_side_def", Once $ definition "add_with_carry'_side_def"] \\
rpt strip_tac >- (
 gs[]
) >- (
 gs[compute_checksum16'_def, add_ones_complement'_def, add_with_carry'_def, AllCaseEqs(), bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
) >- (
 gs[]
) >- (
 gs[bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
) \\
simp[Once $ theorem "compute_checksum16'_side_def", all_lists_length_16_def]
QED
val _ = update_precondition alookup'_inner_side;
val _ = translate ALOOKUP'_def;
val _ = translate Checksum16_get'_def;

val _ = translate vss_ascope_update_def;
val _ = translate vss_ascope_lookup_def;
val _ = translate update_ascope_gen_def;
val _ = translate oTAKE_DROP_def;
val _ = translate set_bit_def;
val _ = translate set_bool_def;
val _ = translate size_in_bits_def;
val _ = translate set_fields_def;
val _ = translate set_header_def;

val _ = translate lookup_ascope_gen_def;
val _ = translate lookup_lval_header_def;
val _ = translate packet_in_extract_gen_def;
val _ = translate vss_packet_in_extract_gen_def;
val _ = translate vss_packet_in_extract'_def;

val _ = translate flatten_v_l_def;
val _ = translate packet_out_emit_gen_def;
val _ = translate vss_packet_out_emit;

val _ = translate vss_pre_deparser_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
