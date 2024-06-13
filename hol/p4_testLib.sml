structure p4_testLib :> p4_testLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax optionSyntax wordsSyntax bitstringSyntax listSyntax numSyntax;

open p4Syntax p4_concurrentSyntax p4_auxTheory p4_exec_semSyntax testLib evalwrapLib p4_vssTheory p4_ebpfTheory;

open p4_exec_semTheory;

open p4_concurrentTheory;

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

fun fixedwidth_freevars_fromindex (fname, start_index, width) =
 mk_list (List.tabulate (width, (fn index => mk_var (fname^(Int.toString (start_index + index)), bool))), bool)
;

fun fixedwidth_freevars (fname, width) =
 fixedwidth_freevars_fromindex (fname, 0, width)
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
    val dscp = fixedwidth_of_int (0, 6);
    (* ECN - ignored, for now. *)
    val ecn = fixedwidth_of_int (0, 2);
    (* Total length - the total length of the packet in bytes, both header and data.
     * Minimum (case no data) is 20. *)
    val data_length = int_of_term $ rhs $ concl $ EVAL (mk_length data);
    val tl = fixedwidth_of_int (20 + data_length, 16);
    (* Identification - ignored, for now. *)
    val id = fixedwidth_of_int (0, 16);
    (* Flags - ignored, for now. *)
    val fl = fixedwidth_of_int (0, 3);
    (* Fragment offset - ignored, for now. *)
    val fo = fixedwidth_of_int (0, 13);
    (* Time to live - should be non-zero. *)
    val ttl = fixedwidth_of_int (ttl, 8);
    (* Protocol - TODO. *)
    val pr = fixedwidth_of_int (0, 8);
    (* Source IP address - TODO *)
    val src = fixedwidth_of_int (0, 32);
    (* Destination IP address - TODO *)
    val dst = fixedwidth_of_int (0, 32);
    (* NOTE: No optional fields here *)

    (* Header checksum - calculated from the other header fields.*)
    val ck = get_ipv4_checksum (version, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, src, dst);
  in
    rhs $ concl $ EVAL $ list_mk_append [version, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, data]
  end
;

(* Same as the above, with symbolic values for the TTL example *)
fun mk_ipv4_packet_ok_ttl data ttl =
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
    val hc = fixedwidth_freevars ("hc", 16);
  in
    rhs $ concl $ EVAL $ list_mk_append [version, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, hc, src, dst, data]
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

fun mk_symb_packet_prefix prefix nbits =
 let
  val bits = fixedwidth_freevars (prefix, nbits);
 in
   bits
 end
;

(* Creates a packet with nbits free variables as bits *)
fun mk_symb_packet nbits =
 (* All bits have same prefix for now. *)
 mk_symb_packet_prefix "i" nbits
;

(* TODO: Do this smarter, with exceptions *)
fun ascope_ty_from_arch arch =
 if arch = "vss"
 then ``:vss_ascope``
 else if arch = "v1model"
 then ``:v1model_ascope``
 else if arch = "ebpf"
 then ``:ebpf_ascope``
 else ``:'a``
;

fun eval_and_print_result arch actx astate nsteps =
 let
  val ascope_ty = ascope_ty_from_arch arch
  val actx' = inst [Type.alpha |-> ascope_ty] actx
 in
  optionSyntax.dest_some $ rhs $ concl $ (fn thm => REWRITE_RULE [(SIMP_CONV (pure_ss++p4_v2w_ss) [] (rhs $ concl thm))] thm) $ EVAL ``arch_multi_exec (^actx') (^astate) ^(term_of_int nsteps)``
end;

(* Used for steps where architecture changes state *)
fun eval_and_print_aenv arch actx astate nsteps =
 el 1 $ snd $ strip_comb $ (eval_and_print_result arch actx astate nsteps);

(* Used for steps inside programmable blocks *)
fun eval_and_print_rest arch actx astate nsteps =
 el 2 $ snd $ strip_comb $ (eval_and_print_result arch actx astate nsteps);

val simple_arith_ss = pure_ss++numSimps.REDUCE_ss

fun the_final_state_imp step_thm = optionSyntax.dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm

fun the_final_state_hyp_imp step_thm =
 let
  val (hyp, step_tm) = dest_imp $ concl step_thm
 in
  (hyp, optionSyntax.dest_some $ snd $ dest_eq step_tm)
 end
;

fun the_final_state_hyp_imp_n step_thm =
 let
  val (hyp, step_tm) = dest_imp $ concl step_thm
  val (exec, final_state) = dest_eq step_tm
  val steps = #3 $ dest_arch_multi_exec exec
 in
  (hyp, optionSyntax.dest_some final_state, steps)
 end
;

fun get_actx step_thm =
 let
  val step_thm_tm = concl step_thm
 in
  #1 $ dest_arch_multi_exec $ fst $ dest_eq $ 
   (if is_imp step_thm_tm
    then snd $ dest_imp $ step_thm_tm
    else step_thm_tm)
 end

(* TODO: Add debug print output *)
(* TODO: Make version that executes until packet is output *)
local
(* Stepwise evaluation under assumptions *)
fun eval_under_assum' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm step_thm 0 = step_thm
  | eval_under_assum' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm step_thm fuel =
 let
  val curr_state = the_final_state_imp step_thm
  val step_thm2 =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never ctxt (mk_arch_multi_exec (ctx, curr_state, 1));
  val comp_step_thm =
   SIMP_RULE simple_arith_ss []
    (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2);
 in
  eval_under_assum' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm comp_step_thm (fuel-1)
 end

in
fun eval_under_assum arch_ty ctx init_astate stop_consts_rewr stop_consts_never ctxt fuel =
 let
  val step_thm =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never ctxt (mk_arch_multi_exec (ctx, init_astate, 1));
  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl;
 in
  if fuel = 1
  then step_thm
  else eval_under_assum' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm step_thm (fuel-1)
 end
end;

(* Successively takes the amount of steps provided in a list *)
local
fun eval_under_assum_break' ctx stop_consts ctxt exec_thm [] = exec_thm
  | eval_under_assum_break' ctx stop_consts ctxt exec_thm (h::t) =
 let
  val init_astate = dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl exec_thm
  val tm = mk_arch_multi_exec (ctx, init_astate, h)
  val exec_thm' = eval_ctxt_gen stop_consts stop_consts ctxt tm
  val exec_comp_thm = MATCH_MP (MATCH_MP arch_multi_exec_comp_n_tl_assl exec_thm) exec_thm'
 in
  eval_under_assum_break' ctx stop_consts ctxt exec_comp_thm t
 end

in
fun eval_under_assum_break ctx init_astate stop_consts ctxt [] =
 let
  val tm = mk_arch_multi_exec (ctx, init_astate, 0)
  val exec_thm = eval_ctxt_gen stop_consts stop_consts ctxt tm
 in
  exec_thm
 end
  | eval_under_assum_break ctx init_astate stop_consts ctxt (h::t) =
 let
  val tm = mk_arch_multi_exec (ctx, init_astate, h)
  val exec_thm = eval_ctxt_gen stop_consts stop_consts ctxt tm
 in
  eval_under_assum_break' ctx stop_consts ctxt exec_thm t
 end
end;

fun the_final_state step_thm = optionSyntax.dest_some $ rhs $ concl step_thm

fun final_state_is_none step_thm = optionSyntax.is_none $ rhs $ concl step_thm

(* Stepwise evaluation *)
local
fun eval_step' actx comp_thm step_thm 0 = step_thm
  | eval_step' actx comp_thm step_thm fuel =
 let
  val curr_state = the_final_state step_thm
  val step_thm2 =
   EVAL “^(mk_arch_multi_exec (actx, curr_state, 1))”;
 in
  if final_state_is_none step_thm2
  then step_thm
  else
   let
    val comp_step_thm =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2);
   in
    eval_step' actx comp_thm comp_step_thm (fuel-1)
   end
 end
in
fun eval_step_fuel ascope_ty actx astate fuel =
 let
  val step_thm =
   EVAL “^(mk_arch_multi_exec (actx, astate, 1))”;
  val comp_thm = INST_TYPE [Type.alpha |-> ascope_ty] arch_multi_exec_comp_n_tl;
 in
  if fuel = 1
  then step_thm
  else eval_step' actx comp_thm step_thm (fuel-1)
 end
end;

(* WARNING: Not guaranteed to terminate! *)
local
fun eval_step' actx comp_thm step_thm =
 let
  val curr_state = the_final_state step_thm
  val step_thm2 =
   EVAL “^(mk_arch_multi_exec (actx, curr_state, 1))”;
 in
  if final_state_is_none step_thm2
  then step_thm
  else
   let
    val comp_step_thm =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2);
   in
    eval_step' actx comp_thm comp_step_thm
   end
 end
in
fun eval_step ascope_ty actx astate =
 let
  val step_thm =
   EVAL “^(mk_arch_multi_exec (actx, astate, 1))”;
  val comp_thm = INST_TYPE [Type.alpha |-> ascope_ty] arch_multi_exec_comp_n_tl;
 in
  if final_state_is_none step_thm
  then raise UNCHANGED
  else eval_step' actx comp_thm step_thm
 end
end;

(* TODO: Move to syntax file *)
(* TODO: This happens to work with all current architectures *)
fun dest_ascope ascope =
 let
  val (counter, ascope') = dest_pair ascope
  val (ext_obj_map, ascope'') = dest_pair ascope'
  val (v_map, ctrl) = dest_pair ascope''
 in
  (counter, ext_obj_map, v_map, ctrl)
 end
;

(* TODO: Move to syntax file *)
(* TODO: This happens to work with all current architectures *)
fun dest_actx actx =
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

(* This tactic is used in the automatic tests derived from the .stf files of the P4 examples *)
local
fun get_existentials eval_thm =
 let
  val final_state = the_final_state eval_thm
  val steps = last $ snd $ strip_comb $ lhs $ concl eval_thm
  val (aenv', g_scope_list', arch_frame_list', status') = dest_astate final_state
  (* TODO: Below line might not generalise well in future if the aenv type changes *)
  val (ab_index', _, _, ascope') = dest_aenv aenv'
 in
  [steps, ab_index', ascope', g_scope_list', arch_frame_list', status']
 end
in
fun p4_eval_test_tac aenv_ty actx astate =
 let
  (* eval_steps repeatedly evaluates until NONE is reached *)
  val step_thm = eval_step aenv_ty actx astate
  val [n, ab_index', ascope', g_scope_list', arch_frame_list', status'] =
   get_existentials step_thm
 in
  (* Perform consecutive exists_tac on all existentially quantified variables in the
   * theorem *)
  (foldr (fn (a, b) => a >> b) ALL_TAC
   (map exists_tac [n, ab_index', ascope', g_scope_list', arch_frame_list', status']))
  >> fs [step_thm, p4_replace_input_def]
 end
end;

(* TODO: Still presupposes VSS? *)
fun debug_arch_from_step arch actx astate nsteps =
 let
  val astate' = eval_and_print_result arch actx astate nsteps
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate'
(* Use the below to debug, e.g. using the executable semantics in p4_exec_semScript.sml: *)
(*  val (i, in_out_list, in_out_list', scope) = dest_aenv aenv *)
(*  val (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) = dest_actx actx *)
 in
  (dest_actx actx, (dest_aenv aenv, g_scope_list, arch_frame_list, status))
 end
;

(* Same as the above, but returns a ctx and a state - use when debugging e.g. eval_step *)
fun debug_arch_from_step_alt arch actx astate nsteps =
 let
  val astate' = eval_and_print_result arch actx astate nsteps
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate'
(* Use the below to debug, e.g. using the executable semantics in p4_exec_semScript.sml: *)
(*  val (i, in_out_list, in_out_list', scope) = dest_aenv aenv *)
(*  val (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) = dest_actx actx *)
 in
  (actx, list_mk_pair [aenv, g_scope_list, arch_frame_list, status])
 end
;

(* TODO: Still presupposes VSS? *)
(* Note that this presupposes execution is inside a programmable block *)
fun debug_frames_from_step arch actx astate nsteps =
 let
  val astate' = eval_and_print_result arch actx astate nsteps
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate'
  val (i, in_out_list, in_out_list', scope) = dest_aenv aenv
  val (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) = dest_actx actx
  val (pbl_x, pbl_el) = dest_arch_block_pbl $ rhs $ concl $ EVAL ``EL (^i) (^ab_list)``
  val (pbl_type, params, b_func_map, decl_list, pars_map, tbl_map) = dest_pblock $ optionSyntax.dest_some $ rhs $ concl $ EVAL ``ALOOKUP (^pblock_map) (^pbl_x)``
  val frame_list = dest_arch_frame_list_regular arch_frame_list
 in
  ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map), (scope, g_scope_list, frame_list, status))
 end
;

fun replace_ext_impl ctx_tm ext_name method_name method_tm =
 let
  val actx_list = spine_pair ctx_tm;

  val actx_list_8first = List.take (actx_list, 8);

  val ext_map = el 9 actx_list;

  val ext_map' =
   let
    val res_opt = rhs $ concl $ EVAL ``ext_map_replace_impl ^ext_map ^(stringLib.fromMLstring ext_name) ^(stringLib.fromMLstring method_name) ^method_tm``;
   in
    if is_some res_opt
    then dest_some res_opt
    else raise (mk_HOL_ERR "p4_testLib" "replace_ext_impl" ("extern name "^ext_name^" and/or method name "^method_name^" could not be found in ext_map"))
   end;

  val actx_list_10 = List.last actx_list;
  val actx_list' = (actx_list_8first@[ext_map'])@[actx_list_10];
  val actx' = list_mk_pair actx_list';
 in
  actx'
 end
;

fun replace_ext_impl ctx_tm ext_name method_name method_tm =
 let
  val actx_list = spine_pair ctx_tm;

  val actx_list_8first = List.take (actx_list, 8);

  val ext_map = el 9 actx_list;

  val ext_map' =
   let
    val res_opt = rhs $ concl $ EVAL ``ext_map_replace_impl ^ext_map ^(stringLib.fromMLstring ext_name) ^(stringLib.fromMLstring method_name) ^method_tm``;
   in
    if is_some res_opt
    then dest_some res_opt
    else raise (mk_HOL_ERR "p4_testLib" "replace_ext_impl" ("extern name "^ext_name^" and/or method name "^method_name^" could not be found in ext_map"))
   end;

  val actx_list_10 = List.last actx_list;
  val actx_list' = (actx_list_8first@[ext_map'])@[actx_list_10];
  val actx' = list_mk_pair actx_list';
 in
  actx'
 end
;

(***********************)
(* Concurrency-related *)

(* TODO: Move to concurrencySyntax *)
fun arch_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
  val aenv = list_mk_pair [n_externs, ext_obj_map, v_map, ctrl]
 in
  if tid = 1
  then list_mk_pair [
        list_mk_pair [index1, io, io', aenv],
        gscope1, arch_frame_list1, status1
       ]
  else list_mk_pair [
        list_mk_pair [index2, io, io', aenv],
        gscope2, arch_frame_list2, status2
       ]
 end
;

(* TODO: Move to concurrencySyntax *)
fun thread_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
 in
  if tid = 1
  then list_mk_pair [index1, gscope1, arch_frame_list1, status1]
  else list_mk_pair [index2, gscope2, arch_frame_list2, status2]
 end
;

fun get_trace_thread_n arch_name actx conc_state nsteps tid =
 let
  val arch_state = arch_state_from_conc_state conc_state tid
  val other_thread_state =
   if tid = 1
   then thread_state_from_conc_state conc_state 2
   else thread_state_from_conc_state conc_state 1

  val arch_exec_thm =
   eval_step_fuel (ascope_ty_from_arch arch_name) actx arch_state nsteps;

  val trace_path_arch_thm = HO_MATCH_MP arch_exec_trace_n arch_exec_thm;

  val trace_path_conc_thm =
   if tid = 1
   then HO_MATCH_MP arch_path_implies_conc_thread1 trace_path_arch_thm
   else HO_MATCH_MP arch_path_implies_conc_thread2 trace_path_arch_thm;
 in
  SPEC other_thread_state trace_path_conc_thm
 end
;

fun get_trace_thread_next_n arch_name actx conc_trace_thm nsteps tid =
 let
  val conc_state_mid = #4 $ dest_trace_path $ concl conc_trace_thm

  val conc_trace_next_n_thm = get_trace_thread_n arch_name actx conc_state_mid nsteps tid
 in
  HO_MATCH_MP (HO_MATCH_MP conc_paths_compose_alt conc_trace_thm) conc_trace_next_n_thm
 end
;

end
