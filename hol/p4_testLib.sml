structure p4_testLib :> p4_testLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax wordsSyntax bitstringSyntax listSyntax numSyntax;

open p4Syntax p4_exec_semSyntax testLib evalwrapLib;

open p4_exec_semTheory;

(* This file contains functions that are useful when creating P4 tests *)

(* NOTE: Hack for obtaining a bitstring from an integer. There's
 * seemingly no function that already does this *)
fun fixedwidth_of_int (value, width) =
  if value < 0
  then
    rhs $ concl $ EVAL (mk_w2v $ mk_word_2comp $ mk_wordii (abs value, width))
  else
    rhs $ concl $ EVAL (mk_w2v $ mk_wordii (value, width))
;

(* This should compute the IPv4 checksum, based on the values of the
 * other fields *)
fun get_ipv4_checksum (version, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, src, dst) =
  let
    val h1 = list_mk_append [version, ihl, dscp, ecn]
    val h2 = tl
    val h3 = id
    val h4 = list_mk_append [fl, fo]
    val h5 = list_mk_append [ttl, pr]
    val h6 = rhs $ concl $ EVAL $ mk_take (term_of_int 16, src)
    val h7 = rhs $ concl $ EVAL $ mk_drop (term_of_int 16, src)
    val h8 = rhs $ concl $ EVAL $ mk_take (term_of_int 16, dst)
    val h9 = rhs $ concl $ EVAL $ mk_drop (term_of_int 16, dst)
    val h_words =
      foldl mk_word_add (mk_v2w (h1, ``:32``))
        (map (fn t => mk_v2w (t, ``:32``)) [h2, h3, h4, h5, h6, h7, h8, h9])
    val h_sum = rhs $ concl $ EVAL h_words
    val h_carry = rhs $ concl $ EVAL (mk_word_slice (``31:num``, ``16:num``, h_sum))
    val h_rem = rhs $ concl $ EVAL (mk_word_slice (``15:num``, ``0:num``, h_sum))
    val h_sum2 = rhs $ concl $ EVAL (mk_word_add (h_rem, h_carry))
    val h_carry2 = rhs $ concl $ EVAL (mk_word_slice (``31:num``, ``16:num``, h_sum2))
    val h_rem2 = rhs $ concl $ EVAL (mk_word_slice (``15:num``, ``0:num``, h_sum2))
    val h_sum3 = rhs $ concl $ EVAL (mk_word_add (h_rem2, h_carry2))
    val h_sum3_1comp =
      rhs $ concl $ EVAL (mk_w2v $ mk_word_1comp $ mk_w2w (h_sum3, ``:16``))
(*
    val verif_sum =
      rhs $ concl $ EVAL (mk_word_add (mk_v2w (h_sum3_1comp, ``:32``), h_sum))
   val verif_carry = rhs $ concl $ EVAL (mk_word_slice (``31:num``, ``16:num``, verif_sum))
    val verif_rem = rhs $ concl $ EVAL (mk_word_slice (``15:num``, ``0:num``, verif_sum))
    val verif_sum2_1comp = rhs $ concl $ EVAL (mk_word_1comp (mk_w2w (mk_word_add (verif_rem, verif_carry), ``:16``)))
    (* Check if verif_sum2_1comp is 0w *)
*)
  in
    h_sum3_1comp
  end
;

fun fixedwidth_freevars (fname, width) =
 mk_list (List.tabulate (width, (fn index => mk_var (fname^(Int.toString index), bool))), bool)
;

(* Creates a bitstring representation of an IPv4 packet, given the
 * bitstring representation of the payload and the
 * time-to-live number *)
(* TODO: Options field is currently always zero *)
fun mk_ipv4_packet_ok data ttl =
  let
    (* IP version - always set to 4 for IPv4 *)
    val version = fixedwidth_of_int (4, 4);
    (* IHL (Internet Header Length) - determines size (in 32-bit words) of IPv4 header.
     * Minimum is 5. *)
    val ihl = fixedwidth_of_int (5, 4);
    (* DSCP - ignored, for now. *)
    val dscp = fixedwidth_freevars ("dscp", 6);
    (* ECN - ignored, for now. *)
    val ecn = fixedwidth_freevars ("ecn", 2);
    (* Total length - the total length of the packet in bytes, both header and data.
     * Minimum (case no data) is 20. *)
    val data_length = int_of_term $ rhs $ concl $ EVAL (mk_length data);
    val tl = fixedwidth_of_int (20 + data_length, 16);
    (* Identification - ignored, for now. *)
    val id = fixedwidth_freevars ("id", 16);
    (* Flags - ignored, for now. *)
    val fl = fixedwidth_freevars ("fl", 3);
    (* Fragment offset - ignored, for now. *)
    val fo = fixedwidth_freevars ("fo", 13);
    (* Time to live - should be non-zero. *)
    val ttl = fixedwidth_of_int (ttl, 8);
    (* Protocol - TODO. *)
    val pr = fixedwidth_freevars ("pr", 8);
    (* Source IP address - TODO *)
    val src = fixedwidth_freevars ("src", 32);
    (* Destination IP address - TODO *)
    val dst = fixedwidth_of_int (0, 32);
    (* NOTE: No optional fields here *)

    (* Header checksum - calculated from the other header fields.*)
    val ck = fixedwidth_of_int (0, 16);
  in
    rhs $ concl $ EVAL $ list_mk_append [version, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, data]
  end
;

(* Creates a bitstring representation of an Ethernet frame, given
 * the bitstring representation of the payload (assumed to be IP). *)
fun mk_eth_frame_ok data =
  let
    (* Destination MAC address - TODO *)
    val src = fixedwidth_of_int (0, 48);
    (* Source MAC address - TODO *)
    val dst = fixedwidth_of_int (0, 48);
    (* EtherType - 0x0800 (2048) signifies IP payload *)
    val ty = fixedwidth_of_int (2048, 16);
    (* CRC Checksum - TODO *)
    val crc = fixedwidth_of_int (0, 32);
  in
    rhs $ concl $ EVAL $ list_mk_append [src, dst, ty, data, crc]
  end
;


fun eval_and_print_result actx astate nsteps =
 optionSyntax.dest_some $ rhs $ concl $ (fn thm => REWRITE_RULE [(SIMP_CONV (pure_ss++p4_v2w_ss) [] (rhs $ concl thm))] thm) $ EVAL ``arch_multi_exec ((^actx):vss_ascope actx) (^astate) ^(term_of_int nsteps)``;

(* Used for steps where architecture changes state *)
fun eval_and_print_aenv actx astate nsteps =
 el 1 $ snd $ strip_comb $ (eval_and_print_result actx astate nsteps);

(* Used for steps inside programmable blocks *)
fun eval_and_print_rest actx astate nsteps =
 el 2 $ snd $ strip_comb $ (eval_and_print_result actx astate nsteps);

(* TODO: Add debug output *)
(* TODO: Make arch_multi_exec syntax file *)
local
fun eval_under_assum' ctx step_thm stop_consts1 stop_consts2 ctxt 0 = step_thm
  | eval_under_assum' ctx step_thm stop_consts1 stop_consts2 ctxt fuel =
 let
  val curr_state = optionSyntax.dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm
  val step_thm2 =
   SPEC_ALL (eval_ctxt_gen stop_consts1 stop_consts2 ctxt (mk_arch_multi_exec (ctx, curr_state, 1)));
  val comp_step_thm =
   SIMP_RULE (pure_ss++numSimps.REDUCE_ss) []
    (HO_MATCH_MP
     (HO_MATCH_MP (INST_TYPE [Type.alpha |-> Type`:vss_ascope`] arch_multi_exec_comp_n_tl_assl) step_thm)
     step_thm2
    );
 in
  eval_under_assum' ctx comp_step_thm stop_consts1 stop_consts2 ctxt (fuel-1)
 end

in
fun eval_under_assum ctx init_astate stop_consts1 stop_consts2 ctxt fuel =
 let
  (* Take the first execution step. *)
  val step_thm =
   SPEC_ALL (eval_ctxt_gen stop_consts1 stop_consts2 ctxt (mk_arch_multi_exec (ctx, init_astate, 1)));
 in
  if fuel = 1
  then step_thm
  else eval_under_assum' ctx step_thm stop_consts1 stop_consts2 ctxt (fuel-1)
 end
end;

(* TODO: Move to syntax file *)
fun dest_astate astate =
 let
  val (aenv, astate') = dest_pair astate
  val (g_scope_list, astate'') = dest_pair astate'
  val (arch_frame_list, status) = dest_pair astate''
 in
  (aenv, g_scope_list, arch_frame_list, status)
 end
;

(* TODO: Move to syntax file *)
fun dest_vss_aenv aenv =
 let
  val (i, aenv') = dest_pair aenv
  val (in_out_list, aenv'') = dest_pair aenv'
  val (in_out_list', ascope) = dest_pair aenv''
 in
  (i, in_out_list, in_out_list', ascope)
 end
;

(* TODO: Move to syntax file *)
fun dest_vss_actx actx =
 let
  val (ab_list, actx') = dest_pair actx
  val (pblock_map, actx'') = dest_pair actx'
  val (ffblock_map, actx''') = dest_pair actx''
  val (input_f, actx'''') = dest_pair actx'''
  val (output_f, actx''''') = dest_pair actx''''
  val (copyin_pbl, actx'''''') = dest_pair actx'''''
  val (copyout_pbl, actx''''''') = dest_pair actx''''''
  val (apply_table_f, actx'''''''') = dest_pair actx'''''''
  val (ext_map, func_map) = dest_pair actx''''''''
 in
  (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
 end
;

fun debug_arch_from_step actx astate nsteps =
 let
  val astate' = eval_and_print_result actx astate nsteps
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate'
(*  val (i, in_out_list, in_out_list', scope) = dest_vss_aenv aenv *)
(*  val (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) = dest_vss_actx actx *)
 in
  (dest_vss_actx actx, (dest_vss_aenv aenv, g_scope_list, arch_frame_list, status))
 end
;

(* Note that this presupposes execution is inside a programmable block *)
fun debug_frames_from_step actx astate nsteps =
 let
  val astate' = eval_and_print_result actx astate nsteps
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate'
  val (i, in_out_list, in_out_list', scope) = dest_vss_aenv aenv
  val (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) = dest_vss_actx actx
  val (pbl_x, pbl_el) = dest_arch_block_pbl $ rhs $ concl $ EVAL ``EL (^i) (^ab_list)``
  val (pbl_type, x_d_list, b_func_map, decl_list, stmt, pars_map, tbl_map) = dest_pblock_regular $ optionSyntax.dest_some $ rhs $ concl $ EVAL ``ALOOKUP (^pblock_map) (^pbl_x)``
  val frame_list = dest_arch_frame_list_regular arch_frame_list
 in
  ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map), (scope, g_scope_list, frame_list, status))
 end
;

end
