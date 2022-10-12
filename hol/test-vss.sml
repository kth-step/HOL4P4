open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

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

(* TODO: Make more realistic data *)
(* NOTE: Data in an IPv4 packet may be a minimum of 0 bytes, maximum of 65536 bytes *)
val input_data_ok = mk_list ([], bool);

(* The simplest IPV4 header that will be judged valid by the example *)
(* NOTE: This only assigns the version, IHL, total length, ttl and header checksum fields. *)
val input_ttl_ok = 1; (* NOTE: TTL 1 will be sent to CPU *)
val input_ipv4_ok = mk_ipv4_packet_ok input_data_ok input_ttl_ok;

(* The simplest ethernet frame that will be judged valid by the example *)
val input_ok = mk_eth_frame_ok input_ipv4_ok;

(*********************)
(*   Initial state   *)
(*********************)

(* OK input at port 1 *)
val init_inlist_ok = mk_list ([pairSyntax.mk_pair (input_ok, input_port_ok)], ``:in_out``);
val init_outlist_ok = mk_list ([], ``:in_out``);

(* TODO: Initialise these with "ARB" instead *)
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

val init_ext_obj_map = ``[(0, INL (core_v_ext_packet_in []));
                          (1, INL (core_v_ext_packet_out []));
                          (2, INL (core_v_ext_packet_out []))]:(num, v_ext) alist``;

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
                    ("parseError", v_err "NoError")]:(string, v) alist``;

(* TODO: More realistic example values *)
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
val init_aenv = ``(^(pairSyntax.list_mk_pair [``0``, init_inlist_ok, init_outlist_ok, ``(^init_ascope)``])):vss_ascope aenv``;

(* TODO: Make syntax functions *)
val init_astate =
 ``(^(pairSyntax.list_mk_pair [init_aenv,
                               listSyntax.mk_list ([vss_init_global_scope], scope_ty),
                               arch_frame_list_empty_tm,
                               status_running_tm])):vss_ascope astate``;

(*******************************************)
(*   Architecture-level semantics tests    *)

val ctx = ``p4_vss_actx``;
val stop_consts1 = [``Checksum16_update``];
val stop_consts2 = []:term list;

val ass1 = gen_all ``Checksum16_update ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list, status) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     SOME ((counter, AUPDATE ext_obj_map (i, INR (vss_v_ext_ipv4_checksum (0w:word16))), v_map, ctrl), g_scope_list, scope_list, status_returnv v_bot)
    | _ => NONE)
  | _ => NONE``;
val ctxt = [ass1];

(* Takes around 45 seconds to run *)
(* 171 steps for TTL=1 packet to get forwarded to CPU *)
eval_under_assum ctx init_astate stop_consts1 stop_consts2 ctxt 171;
