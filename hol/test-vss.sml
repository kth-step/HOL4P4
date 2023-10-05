open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax wordsSyntax listSyntax bitstringSyntax numSyntax;
open p4Syntax;
open testLib;
open p4Lib p4_coreLib p4_vssLib p4_testLib;
open p4_exec_semTheory p4_coreTheory p4_vssTheory p4_vss_exampleTheory;
open blastLib;
open computeLib;
open alistTheory;

(* This file includes complete test runs of the VSS example in the P4 spec. *)

(*********************)
(*   Input packets   *)
(*********************)

(* TODO: Currently the input is Ethernet frames *)

val input_port_ok = ``1:num``;

(* NOTE: Data in an IPv4 packet may be a minimum of 0 bytes, maximum of 65536 bytes *)
val input_data_ok = mk_list ([], bool);

(* The simplest IPV4 header that will be judged valid by the example *)
(* NOTE: This only assigns the version, IHL, total length, ttl and header checksum fields. *)
val input_ttl_ok = 2; (* NOTE: TTL 1 will be sent to CPU *)
val input_ipv4_ok = mk_ipv4_packet_ok input_data_ok input_ttl_ok;

(* The simplest ethernet frame that will be judged valid by the example *)
val input_ok = mk_eth_frame_ok input_ipv4_ok;

(*********************)
(*   Initial state   *)
(*********************)

(* OK input at port 1 *)
val init_inlist_ok = mk_list ([pairSyntax.mk_pair (input_ok, input_port_ok)], ``:in_out``);
val init_outlist_ok = mk_list ([], ``:in_out``);

val ipv4_header_uninit =
 mk_v_header_list F 
                  [(``"version"``, mk_v_biti_arb 4),
                   (``"ihl"``, mk_v_biti_arb 4),
                   (``"diffserv"``, mk_v_biti_arb 8),
                   (``"totalLen"``, mk_v_biti_arb 16),
                   (``"identification"``, mk_v_biti_arb 16),
                   (``"flags"``, mk_v_biti_arb 3),
                   (``"fragOffset"``, mk_v_biti_arb 13),
                   (``"ttl"``, mk_v_biti_arb 8),
                   (``"protocol"``, mk_v_biti_arb 8),
                   (``"hdrChecksum"``, mk_v_biti_arb 16),
                   (``"srcAddr"``, mk_v_biti_arb 32),
                   (``"dstAddr"``, mk_v_biti_arb 32)];

val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_biti_arb 48),
                   (``"srcAddr"``, mk_v_biti_arb 48),
                   (``"etherType"``, mk_v_biti_arb 16)];

val parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];


val init_counter = ``3:num``;

val init_ext_obj_map = ``[(0, INL (core_v_ext_packet []));
                          (1, INL (core_v_ext_packet []));
                          (2, INL (core_v_ext_packet []))]:(num, (core_v_ext + vss_v_ext)) alist``;

(* All variables used in the architectural scope need to be declared *)
(* NOTE: the output packet is here called "data_crc". VSS spec has both input and output called "b" *)
val init_v_map = ``[("inCtrl", v_struct [("inputPort", ^(mk_v_biti_arb 4))]);
                    ("outCtrl", v_struct [("outputPort", ^(mk_v_biti_arb 4))]);
                    ("b_in", v_ext_ref 0);
                    ("b_out", v_ext_ref 1);
                    ("data_crc", v_ext_ref 2);
                    ("parsedHeaders", (^parsed_packet_struct_uninit));
                    ("headers", (^parsed_packet_struct_uninit));
                    ("outputHeaders", (^parsed_packet_struct_uninit));
                    ("parseError", ^(mk_v_bitii (0,32)))]:(string, v) alist``;

(* Regular ethernet output ports are numbered 0-7 *)
val init_ctrl = ``[("ipv4_match",
                    (* IPv4 matching maps IP destination address to
                     * a next hop IPv4 address and output port *)
                    [( [e_v ^(mk_v_bitii (0,32))],
                       ("Set_nhop", [e_v ^(mk_v_bitii (1,32));
                                     e_v ^(mk_v_bitii (0,4))]) )]
                   );
                   ("dmac",
                    (* Destination MAC addess is computed from next hop IPv4 address *)
                    [( [e_v ^(mk_v_bitii (1,32))],
                       ("Set_dmac", [e_v ^(mk_v_bitii (1,48))]) )]
                   );
                   ("smac",
                    (* Source MAC addess is computed from output port *)
                    [( [e_v ^(mk_v_bitii (0,4))],
                       ("Set_smac", [e_v ^(mk_v_bitii (0,48))]) )]
                   )]``;

(* TODO: Make syntax functions *)
val init_ascope = ``((^init_counter), (^init_ext_obj_map), (^init_v_map), ^init_ctrl):vss_ascope``;

(* TODO: Make syntax functions *)
val init_aenv = ``(^(pairSyntax.list_mk_pair [``0:num``, init_inlist_ok, init_outlist_ok, ``(^init_ascope)``])):vss_ascope aenv``;

(* TODO: Make syntax functions *)
val init_astate =
 ``(^(pairSyntax.list_mk_pair [init_aenv,
                               listSyntax.mk_list ([vss_init_global_scope], scope_ty),
                               arch_frame_list_empty_tm,
                               status_running_tm])):vss_ascope astate``;

(*******************************************)
(*   Architecture-level semantics tests    *)

(* Single reduction: *)
EVAL ``arch_exec p4_vss_actx (^init_astate)``;

(* Expanded shorthand: *)
val vss_actx = rhs $ concl $ EVAL ``p4_vss_actx``;

(* Multiple reductions: *)
(* In V1, this ended at 131 steps for TTL=1 in input *)
(* In V2, this ends at 210 steps for TTL=1 in input *)

(*
val nsteps = 63;
val astate = init_astate;
val actx = vss_actx;
*)

(* FOR DEBUGGING:

val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', ascope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "vss" actx astate nsteps;

val [counter, ext_obj_map, v_map, ctrl] = spine_pair ascope;


val test = rhs $ concl $ EVAL ``EL ^i ^ab_list``;
val x = ``"parser"``;
val test = rhs $ concl $ EVAL ``ALOOKUP ^pblock_map ^x``;
val test = rhs $ concl $ EVAL ``^copyout_pbl (^g_scope_list, ^ascope, [d_none; d_out], ["b"; "p"], set_fin_status pbl_type_parser ^status)``;

val test = rhs $ concl $ EVAL ``copyout ["b"; "p"] [d_none; d_out] [ [] ; [] ] [v_map_to_scope ^v_map] ^g_scope_list``;

val test = rhs $ concl $ EVAL ``update_return_frame ["b"; "p"] [d_none; d_out] ([v_map_to_scope ^v_map]++[ [] ; [] ]) [LAST ^g_scope_list]``;

(********** Nested exec sems ***********)

(* NOTE: For debugging frames_exec *)
val ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map), (scope, g_scope_list, frame_list, status)) = debug_frames_from_step actx astate nsteps;

(* NOTE: New g_scope_list from scopes_to_pass, use to debug stmt_exec *)
val g_scope_list' = optionSyntax.dest_some $ rhs $ concl $ EVAL ``scopes_to_pass (funn_name "pipe") ^func_map ^b_func_map ^g_scope_list``;
val b_func_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL ``map_to_pass (funn_name "pipe") ^b_func_map``;
val tbl_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL ``tbl_to_pass (funn_name "pipe") ^b_func_map ^tbl_map``;

(* NOTE: For debugging stmt_exec (top element of frame list) *)
val frame_list = ``[(funn_ext "packet_out" "emit",
      [stmt_seq stmt_ext (stmt_ret (e_v v_bot))],
      [[(varn_name "this",v_ext_ref 0,NONE);
        (varn_name "data",
         v_header T
           [("dstAddr",v_bit (w2v:word48 -> bool list 1w,48)); ("srcAddr",v_bit (w2v:word48 -> bool list 0w,48));
            ("etherType",v_bit (w2v:word16 -> bool list 2048w,16))],NONE)]])]:frame_list``;

(* stmt_exec test: *)
val [ascope', g_scope_list', frame_list', status'] = spine_pair $ optionSyntax.dest_some $ rhs $ concl $ EVAL ``stmt_exec (^apply_table_f, ^ext_map, ^func_map, ^b_func_map, ^pars_map, ^tbl_map) (^scope, ^g_scope_list', ^frame_list, status_running)``

*)

(* TODO: Make "exec arch block" function *)

(* arch_in: input read into b, data_crc and inCtrl *)
eval_and_print_aenv "vss" vss_actx init_astate 1;

(* arch_pbl_init: parser block arguments read into b and p *)
eval_and_print_rest "vss" vss_actx init_astate 2;

(* After a number of arch_pbl_exec steps: status set to status_trans "accept" *)
eval_and_print_rest "vss" vss_actx init_astate 63;

(* arch_pbl_ret: parsedHeaders copied out to arch scope *)
eval_and_print_aenv "vss" vss_actx init_astate 64;

(* arch_ffbl: Parser Runtime *)
eval_and_print_aenv "vss" vss_actx init_astate 65;

(* arch_pbl_init: arguments read into pbl-global scope, frame initialised *)
eval_and_print_rest "vss" vss_actx init_astate 66;

(* arch_control_exec: *)
eval_and_print_rest "vss" vss_actx init_astate 140;

(* arch_pbl_ret: outCtrl written to arch scope *)
eval_and_print_aenv "vss" vss_actx init_astate 141;

(* arch_ffbl: pre-Deparser *)
eval_and_print_aenv "vss" vss_actx init_astate 142;

(* arch_pbl_init: arguments read into pbl-global scope, frame initialised *)
eval_and_print_rest "vss" vss_actx init_astate 143;

(* arch_pbl_exec *)
eval_and_print_rest "vss" vss_actx init_astate 193;

(* arch_pbl_ret: p written to arch scope *)
eval_and_print_aenv "vss" vss_actx init_astate 194;

(* arch_out: output read into output stream *)
eval_and_print_aenv "vss" vss_actx init_astate 195;
