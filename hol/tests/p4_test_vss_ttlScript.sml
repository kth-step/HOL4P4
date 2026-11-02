Theory p4_test_vss_ttl
Ancestors
  p4_exec_sem p4_core p4_vss p4_vss_example alist
Libs
  pairSyntax wordsSyntax listSyntax numSyntax p4Syntax p4_vssLib p4_testLib

(* This file includes complete test runs of the VSS example in the P4 spec for a TTL that is low enough to send the packet to CPU, with the bits in other fields that don't affect this computation set to free variables. The CPU port gets the original frame (spec 5.2.3). A TTL 2 packet is forwarded with the updated checksum. *)

(******************************)
(*   Example program terms    *)
(******************************)

(*********************)
(*   Input packets   *)

(* TODO: Currently the input is Ethernet frames *)

val input_port_ok = ``1:num``;

(* NOTE: Data in an IPv4 packet may be a minimum of 0 bytes, maximum of 65536 bytes *)
val input_data_ok = mk_list ([], bool);

(* The simplest IPV4 header that will be judged valid by the example *)
(* NOTE: This only assigns the version, IHL, total length, ttl and header checksum fields. *)
val input_ttl_ok = 1; (* NOTE: TTL 1 will be sent to CPU *)
val input_ipv4_ok = mk_ipv4_packet_ok_ttl input_data_ok input_ttl_ok;

(* The simplest ethernet frame that will be judged valid by the example *)
val input_ok = mk_eth_frame_ok input_ipv4_ok;

(*********************)
(*   Initial state   *)

(* OK input at port 1 *)
val init_inlist_ok = mk_list ([mk_pair (input_ok, input_port_ok)], ``:in_out``);
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


val init_counter = ``4:num``;

val init_ext_obj_map = ``[(0, INL (core_v_ext_packet []));
                          (1, INL (core_v_ext_packet []));
                          (2, INL (core_v_ext_packet []));
                          (3, INL (core_v_ext_packet []))]:(num, (core_v_ext + vss_v_ext)) alist``;

(* All variables used in the architectural scope need to be declared *)
(* NOTE: the unparsed rest of the frame is called "payload" and the original frame "b_orig".
 * VSS spec has both input and output called "b" *)
val init_v_map = ``[("inCtrl", v_struct [("inputPort", ^(mk_v_biti_arb 4))]);
                    ("outCtrl", v_struct [("outputPort", ^(mk_v_biti_arb 4))]);
                    ("b_in", v_ext_ref 0);
                    ("b_out", v_ext_ref 1);
                    ("payload", v_ext_ref 2);
                    ("b_orig", v_ext_ref 3);
                    ("parsedHeaders", (^parsed_packet_struct_uninit));
                    ("headers", (^parsed_packet_struct_uninit));
                    ("outputHeaders", (^parsed_packet_struct_uninit));
                    ("parseError", ^(mk_v_bitii (0,32)))]:(string, v) alist``;

(* Regular ethernet output ports are numbered 0-7 *)
val init_ctrl = ``[("ipv4_match",
                    (* IPv4 matching maps IP destination address to
                     * a next hop IPv4 address and output port *)
                    [(($= [e_v ^(mk_v_bitii (0,32))] , 0:num),
                       ("Set_nhop", [e_v ^(mk_v_bitii (1,32));
                                     e_v ^(mk_v_bitii (0,4))]) )]
                   );
                   ("dmac",
                    (* Destination MAC addess is computed from next hop IPv4 address *)
                    [(($= [e_v ^(mk_v_bitii (1,32))], 0),
                       ("Set_dmac", [e_v ^(mk_v_bitii (1,48))]) )]
                   );
                   ("check_ttl",
                    (* A packet whose TTL has reached 0 goes to the CPU *)
                    [(($= [e_v ^(mk_v_bitii (0,8))], 0),
                       ("Send_to_cpu", []) )]
                   );
                   ("smac",
                    (* Source MAC addess is computed from output port *)
                    [(($= [e_v ^(mk_v_bitii (0,4))], 0),
                       ("Set_smac", [e_v ^(mk_v_bitii (0,48))]) )]
                   )]``;

(* TODO: Make syntax functions *)
val init_ascope = ``((^init_counter), (^init_ext_obj_map), (^init_v_map), ^init_ctrl, 0):vss_ascope``;

(* TODO: Make syntax functions *)
val init_aenv = ``(^(list_mk_pair [``0:num``, init_inlist_ok, init_outlist_ok, ``(^init_ascope)``])):vss_ascope aenv``;

(* TODO: Make syntax functions *)
(* The initial architectural state *)
val init_astate =
 ``(^(pairSyntax.list_mk_pair [init_aenv,
                               mk_list ([vss_init_global_scope], scope_ty),
                               arch_frame_list_empty_tm,
                               status_running_tm])):vss_ascope astate``;

(***************************************)
(*   Data non-interference theorems    *)
(***************************************)

val ctx = ``p4_vss_actx r``;
val stop_consts_rewr = [``compute_checksum16``];
Definition vss_updated_checksum16_def:
 vss_updated_checksum16 (w16_list:bool list) = 
  word_1comp (sub_ones_complement (0xFEFFw, v2w w16_list)):word16
End
val stop_consts_never = [``vss_updated_checksum16``];

val ass1 =
 ``compute_checksum16
    [v2w [F; T; F; F; F; T; F; T; dscp0; dscp1; dscp2; dscp3;
	  dscp4; dscp5; ecn0; ecn1];
     v2w [F; F; F; F; F; F; F; F; F; F; F; T; F; T; F; F];
     v2w [id0; id1; id2; id3; id4; id5; id6; id7; id8; id9; id10;
	  id11; id12; id13; id14; id15];
     v2w [fl0; fl1; fl2; fo0; fo1; fo2; fo3; fo4; fo5; fo6; fo7;
	  fo8; fo9; fo10; fo11; fo12];
     v2w [F; F; F; F; F; F; F; T; pr0; pr1; pr2; pr3; pr4; pr5;
	  pr6; pr7];
     v2w [hc0; hc1; hc2; hc3; hc4; hc5; hc6; hc7; hc8; hc9; hc10; hc11; hc12;
	  hc13; hc14; hc15];
     v2w [src0; src1; src2; src3; src4; src5; src6; src7; src8;
	  src9; src10; src11; src12; src13; src14; src15];
     v2w [src16; src17; src18; src19; src20; src21; src22; src23;
	  src24; src25; src26; src27; src28; src29; src30; src31];
     v2w [F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F];
     v2w [F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F]] = (0w:word16)``;

(* New result due to updated TTL value: same as if 0x0100 and the previous checksum was no longer added to the sum *)
val ass2 =
 ``compute_checksum16
    [v2w [F; T; F; F; F; T; F; T; dscp0; dscp1; dscp2; dscp3;
	  dscp4; dscp5; ecn0; ecn1];
     v2w [F; F; F; F; F; F; F; F; F; F; F; T; F; T; F; F];
     v2w [id0; id1; id2; id3; id4; id5; id6; id7; id8; id9; id10;
	  id11; id12; id13; id14; id15];
     v2w [fl0; fl1; fl2; fo0; fo1; fo2; fo3; fo4; fo5; fo6; fo7;
	  fo8; fo9; fo10; fo11; fo12];
     v2w [F; F; F; F; F; F; F; F; pr0; pr1; pr2; pr3; pr4; pr5;
	  pr6; pr7];
     v2w [F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F];
     v2w [src0; src1; src2; src3; src4; src5; src6; src7; src8;
	  src9; src10; src11; src12; src13; src14; src15];
     v2w [src16; src17; src18; src19; src20; src21; src22; src23;
	  src24; src25; src26; src27; src28; src29; src30; src31];
     v2w [F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F];
     v2w [F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F]] = vss_updated_checksum16 [hc0; hc1; hc2; hc3; hc4; hc5; hc6; hc7; hc8; hc9; hc10; hc11; hc12; hc13; hc14; hc15]``;
val ctxt = CONJ (ASSUME ass1) (ASSUME ass2);

(*************************************************)
(* Version 1: Use stepwise EVAL with assumptions *)
(* Takes around 20 seconds to run *)

(* 185 steps for TTL=1 packet to reach the output block *)

(* Theorem on line below proves data non-interference using proof approach 1 *)
GEN_ALL $ eval_under_assum vss_arch_ty ctx init_astate stop_consts_rewr stop_consts_never ctxt 185;


(************************************************************************************************************)
(* Version 2: Use EVAL directly with re-defined function that has a property that easily enables the theorem.
 * This re-defined function should have no effect on the theorem statement other than through this property *)
(* Takes around 2 seconds to run *)

(* Re-definition of Checksum16_get *)
Definition Checksum16_get':
 (Checksum16_get' ((counter, ext_obj_map, v_map, ctrl):vss_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case ALOOKUP ext_obj_map i of
    | SOME (INR (vss_v_ext_ipv4_checksum ipv4_checksum)) =>
     SOME ((counter, ext_obj_map, v_map, ctrl):vss_ascope, scope_list, status_returnv (v_bit (w16 0w)))
    | _ => NONE)
  | _ => NONE
 )
End

(*
val ctx_tm = (rhs $ concl p4_vss_actx_def)
val ext_name = "Checksum16"
val method_name = "get"
val method_tm = “Checksum16_get'”
*)

(* Re-definition of p4_vss_actx' *)
Definition p4_vss_actx'_def:
  p4_vss_actx' r = ^(replace_ext_impl (rhs $ snd $ strip_forall $ concl p4_vss_actx_def) "Checksum16" "get" “Checksum16_get'”)
End
val ctx' = ``p4_vss_actx' r``;

(* EVAL-uate until packet is output (happens to be step 186) *)
(* Theorem on line below proves data non-interference using proof approach 2 *)
GEN_ALL $ EVAL ``arch_multi_exec (^ctx') (^init_astate) 186``;


(**************************************************)
(* Version 3: Use repeated EVAL-under-assumptions *)
(* Takes around 2 seconds to run *)

(* Takes 68 steps, then another 104, then 14 *)
(* Theorem on line below proves data non-interference using proof approach 3 *)
GEN_ALL $ eval_under_assum_break ctx init_astate (stop_consts_rewr@stop_consts_never) ctxt [68, 104, 14];


(**************************************************************************************)
(* TTL 2: the packet leaves on port 0 with TTL 1, the incrementally updated checksum and dstAddr 1 *)

val input_fwd = mk_eth_frame_ok (mk_ipv4_packet_ok_ttl input_data_ok 2);
val init_aenv_fwd = ``(^(list_mk_pair [``0:num``, mk_list ([mk_pair (input_fwd, input_port_ok)], ``:in_out``), init_outlist_ok, ``(^init_ascope)``])):vss_ascope aenv``;
val init_astate_fwd =
 ``(^(pairSyntax.list_mk_pair [init_aenv_fwd,
                               mk_list ([vss_init_global_scope], scope_ty),
                               arch_frame_list_empty_tm,
                               status_running_tm])):vss_ascope astate``;

fun ttl_bits ttl = rhs $ concl $ EVAL ``fixwidth 8 (n2v ^(term_of_int ttl))``;

(* ass1 and ass2 with the TTL word one higher *)
val ttl_word = fn ttl => ``v2w (^(ttl_bits ttl) ++ [pr0; pr1; pr2; pr3; pr4; pr5; pr6; pr7]):word16``;
val ass1_fwd = subst [rhs (concl (EVAL (ttl_word 1))) |-> rhs (concl (EVAL (ttl_word 2)))] ass1;
val ass2_fwd = subst [rhs (concl (EVAL (ttl_word 0))) |-> rhs (concl (EVAL (ttl_word 1)))] ass2;
val ctxt_fwd = CONJ (ASSUME ass1_fwd) (ASSUME ass2_fwd);

(* The packet is output after 210 steps *)
val fwd_thm = GEN_ALL $ eval_under_assum vss_arch_ty ctx init_astate_fwd stop_consts_rewr stop_consts_never ctxt_fwd 210;

val expected_fwd =
 let
  val bits = fst $ dest_list input_fwd
  val csum = ``vss_updated_checksum16 [hc0; hc1; hc2; hc3; hc4; hc5; hc6; hc7; hc8; hc9; hc10; hc11; hc12; hc13; hc14; hc15]``
  val csum_bits = map (fn k => fcpSyntax.mk_fcp_index (csum, term_of_int k)) (List.tabulate (16, fn k => 15 - k))
  val dst_bits = fst $ dest_list $ rhs $ concl $ EVAL ``fixwidth 48 (n2v 1)``
 in
  mk_list (dst_bits @ List.take (List.drop (bits, 48), 128) @ fst (dest_list (ttl_bits 1)) @ List.take (List.drop (bits, 184), 8) @ csum_bits @ List.drop (bits, 208), bool)
 end;
val _ =
 if term_eq (#3 $ dest_aenv $ #1 $ dest_astate $ optionSyntax.dest_some $ rhs $ snd $ strip_imp $ snd $ strip_forall $ concl fwd_thm)
            (mk_list ([mk_pair (expected_fwd, ``0:num``)], ``:in_out``))
 then ()
 else raise Fail "the forwarded frame is not the input frame with dstAddr 1, TTL 1 and the updated checksum";
