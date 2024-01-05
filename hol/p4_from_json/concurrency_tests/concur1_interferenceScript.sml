open HolKernel Parse bossLib boolSyntax boolLib liteLib simpLib;

val _ = new_theory "concur1_interference";

open p4_testLib p4_arch_auxTheory;
open p4_concurrentTheory p4_v1modelTheory;
open bitstringTheory;

open pairSyntax p4Syntax p4_concurrentSyntax p4_v1modelLib;

val concur1_actx = ``([arch_block_inp;
  arch_block_pbl "MyParser"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "MyVerifyChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyIngress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyEgress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyComputeChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyDeparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("MyParser",
   pblock_regular pbl_type_parser
     [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
       [("packet",d_none); ("hdr",d_out); ("meta",d_inout);
        ("standard_metadata",d_inout)])] []
     [("start",stmt_seq stmt_empty (stmt_trans (e_v (v_str "accept"))))] []);
  ("MyVerifyChecksum",
   pblock_regular pbl_type_control
     [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,
       [("hdr",d_inout); ("meta",d_inout)])] [] [] []);
  ("MyIngress",
   pblock_regular pbl_type_control
     [("read_register",
       stmt_seq
         (stmt_seq
            (stmt_ass lval_null
               (e_call (funn_ext "register" "read")
                  [e_var (varn_name "r"); e_var (varn_name "tmp");
                   e_v
                     (v_bit
                        ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                          F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],32))]))
            (stmt_ass (lval_varname (varn_name "tmp"))
               (e_binop (e_var (varn_name "tmp")) binop_add
                  (e_v
                     (v_bit
                        ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],16))))))
         (stmt_ret (e_v v_bot)),[]);
      ("write_register",
       stmt_seq
         (stmt_ass lval_null
            (e_call (funn_ext "register" "write")
               [e_var (varn_name "r");
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; F],32));
                e_var (varn_name "tmp")])) (stmt_ret (e_v v_bot)),[]);
      ("MyIngress",
       stmt_seq
         stmt_empty
         (stmt_block []
            (stmt_seq (stmt_app "flowlet" []) (stmt_app "new_flowlet" []))),
       [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)])]
     [(varn_name "tmp",tau_bit 16,NONE)] []
     [("flowlet",[],"read_register",[]);
      ("new_flowlet",[],"write_register",[])]);
  ("MyEgress",
   pblock_regular pbl_type_control
     [("MyEgress",stmt_seq stmt_empty stmt_empty,
       [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)])]
     [] [] []);
  ("MyComputeChecksum",
   pblock_regular pbl_type_control
     [("MyComputeChecksum",stmt_seq stmt_empty stmt_empty,
       [("hdr",d_inout); ("meta",d_inout)])] [] [] []);
  ("MyDeparser",
   pblock_regular pbl_type_control
     [("MyDeparser",stmt_seq stmt_empty stmt_empty,
       [("packet",d_none); ("hdr",d_in)])] [] [] [])],
 [("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f (v_struct [],v_struct []),v1model_output_f,
 v1model_copyin_pbl,v1model_copyout_pbl,v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)])],
 [("NoAction",stmt_seq stmt_empty (stmt_ret (e_v v_bot)),[])]):v1model_ascope actx``;

val concur1_astate =
 ``((0, (* Block index *)
     [([T], 1:num); ([F], 2)], (* Input list *)
     [], (* Output list *)
     (* 'a: *)
     1, (* Number of extern objects *)
     [(0, INR (v1model_v_ext_register [(fixwidth 16 [], 16)]))],
     (^v1model_init_v_map++["r", v_ext_ref 0]),
     [("flowlet",[]); ("new_flowlet",[])]), (* End of 'a env *)
    [[(varn_name "r", (v_ext_ref 0, NONE))]], (* g_scope_list *)
    arch_frame_list_empty, (* frame_list *)
    status_running (* status *)
   ):v1model_ascope astate``;

val concur1_shared_s =
 ``([([T], 1:num); ([F], 2)], (* Input list *)
    []: (bool list # num) list, (* Output list *)
    (* 'a: *)
    (1:num, (* Number of extern objects *)
     [(0:num, INR (v1model_v_ext_register [(fixwidth 16 [], 16)]))]:(num # (core_v_ext + v1model_v_ext)) list,
     (^v1model_init_v_map++["r", v_ext_ref 0]),
     [("flowlet",[]:(((e list -> bool) # num) # string # e list) list); ("new_flowlet",[])])
   )``;

val concur1_t1_s =
 ``(0:num,
    [[(varn_name "r", (v_ext_ref 0, NONE))]]:scope list,
    arch_frame_list_empty,
    status_running
   )``;

val concur1_t2_s =
 ``(0:num,
    [[(varn_name "r", (v_ext_ref 0, NONE))]]:scope list,
    arch_frame_list_empty,
    status_running
   )``;

(*
(* 28 steps to finishing first function *)
 val (_, ((i, _, in_out_list', _), _, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 28

(* 55 steps to finishing the entire program *)
 val (_, ((i, _, in_out_list', _), _, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 55

First witness from
  T1: 55 steps
  T2: 55 steps

Second witness from
  T1: 28 steps
  T2: 28 steps
  T1: 27 steps
  T2: 27 steps

 val (_, ((i, _, in_out_list', _), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 55
*)

val (_, ((i1', _, _, _), g_scope_list1', arch_frame_list1', status1')) = debug_arch_from_step "v1model" concur1_actx concur1_astate 55

val t1_s' = “(0:num, ^g_scope_list1', arch_frame_list_empty, status_running)”;
val t2_s' = “(0:num, ^g_scope_list1', arch_frame_list_empty, status_running)”;

(*
val (_, ((_, io_list, io_list', ascope'), _, _, _)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 55
*)

val shared_s'_standard_metadata =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(``"ingress_port"``, mk_v_bitii (2, 9)),
    (``"egress_spec"``, mk_v_bitii (0, 9)),
    (``"egress_port"``, mk_v_bitii (0, 9)),
    (``"instance_type"``, mk_v_bitii (0, 32)),
    (``"packet_length"``, mk_v_bitii (0, 32)),
    (``"enq_timestamp"``, mk_v_bitii (0, 32)),
    (``"enq_qdepth"``, mk_v_bitii (0, 19)),
    (``"deq_timedelta"``, mk_v_bitii (0, 32)),
    (``"deq_qdepth"``, mk_v_bitii (0, 19)),
    (``"ingress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"egress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"mcast_grp"``, mk_v_bitii (0, 16)),
    (``"egress_rid"``, mk_v_bitii (0, 16)),
    (``"checksum_error"``, mk_v_bitii (0, 1)),
    (``"parser_error"``, mk_v_bitii (0, 32)),
    (``"priority"``, mk_v_bitii (0, 3))],
   “:(string # v)”);
val shared_s' =
“([]:(bool list # num) list,[([F], 0:num); ([F], 0)],5:num,
  [(0:num,INR (v1model_v_ext_register [(w2v (1w:word16),16)]));
   (1,INL (core_v_ext_packet [])); (2,INL (core_v_ext_packet [T]));
   (3,INL (core_v_ext_packet [])); (4,INL (core_v_ext_packet [F]))],
  [("parseError",v_bit (w2v (0w:word32),32)); ("r",v_ext_ref 0); ("b",v_ext_ref 3);
   ("b_temp",v_ext_ref 4);
   ("standard_metadata",
    v_struct ^shared_s'_standard_metadata);
   ("parsedHdr",v_struct []); ("hdr",v_struct []); ("meta",v_struct [])],
  [("flowlet",[]:(((e list -> bool) # num) # string # e list) list); ("new_flowlet",[])])”;

val shared_s'' =
“([]:(bool list # num) list,[([T], 0:num); ([F], 0)],5:num,
  [(0:num,INR (v1model_v_ext_register [(w2v (2w:word16),16)]));
   (1,INL (core_v_ext_packet [])); (2,INL (core_v_ext_packet [T]));
   (3,INL (core_v_ext_packet [])); (4,INL (core_v_ext_packet [F]))],
  [("parseError",v_bit (w2v (0w:word32),32)); ("r",v_ext_ref 0); ("b",v_ext_ref 3);
   ("b_temp",v_ext_ref 4);
   ("standard_metadata",
    v_struct ^shared_s'_standard_metadata);
   ("parsedHdr",v_struct []); ("hdr",v_struct []); ("meta",v_struct [])],
  [("flowlet",[]:(((e list -> bool) # num) # string # e list) list); ("new_flowlet",[])])”;

val init_conc_state = list_mk_pair[concur1_shared_s, concur1_t1_s, concur1_t2_s];

val trace1_thm =
 let
  val thm1 = get_trace_thread_n "v1model" concur1_actx init_conc_state 28 1
  val thm2 = get_trace_thread_next_n "v1model" concur1_actx thm1 28 2
  val thm3 = get_trace_thread_next_n "v1model" concur1_actx thm2 27 1
  val thm4 = get_trace_thread_next_n "v1model" concur1_actx thm3 27 2
 in
  thm4
 end;

val trace2_thm =
 let
  (* Call 1: to get_trace_thread_n *)
  val thm1 = get_trace_thread_n "v1model" concur1_actx init_conc_state 55 1

  (* Call 2: Should be to a new to get_trace_thread_next_n that continues from a theorem *)
  val thm2 = get_trace_thread_next_n "v1model" concur1_actx thm1 55 2
 in
  thm2
 end;

Theorem concur1_trace_path_interference:
?n t1_s' t2_s' shared_s' shared_s''.
  (trace_path ( \s s'. conc_red ^concur1_actx s s') n (^concur1_shared_s, (^concur1_t1_s, ^concur1_t2_s))
                                            (shared_s', (t1_s', t2_s')) /\
   p4_conc_finished (shared_s', (t1_s', t2_s')) /\
   v1model_ascope_read_ext_obj (v1model_ascope_of_conc_state shared_s') "r" =
    SOME (INR (v1model_v_ext_register [(fixwidth 16 (n2v 1), 16)]))) /\
  (trace_path ( \s s'. conc_red ^concur1_actx s s') n (^concur1_shared_s, (^concur1_t1_s, ^concur1_t2_s))
                                            (shared_s'', (t1_s', t2_s')) /\
   p4_conc_finished (shared_s'', (t1_s', t2_s')) /\
   v1model_ascope_read_ext_obj (v1model_ascope_of_conc_state shared_s'') "r" =
    SOME (INR (v1model_v_ext_register [(fixwidth 16 (n2v 2), 16)])))
Proof
EXISTS_TAC “110:num” >>
EXISTS_TAC t1_s' >>
EXISTS_TAC t2_s' >>
EXISTS_TAC shared_s' >>
EXISTS_TAC shared_s'' >>
CONJ_TAC >| [
 rpt strip_tac >| [
  (* 1. For witness of r=1, t1 executes the first function, then t2 executes the first function, then t1 the rest, then t2 the rest. *)
  ASSUME_TAC trace1_thm >>
  gvs [w2v_def],

  fs[p4_conc_finished_def],

  fs[v1model_ascope_of_conc_state_def, v1model_ascope_read_ext_obj_def] >>
  EVAL_TAC
 ],

 rpt strip_tac >| [
  (* 2. For witness of r=2, use executable semantics, then arch_exec_trace_n,
   * then arch_path_implies_conc_thread1, then executable semantics for thread 2, then
   * arch_exec_trace_n, then arch_path_implies_conc_thread2, then conc_paths_compose. *)
  ASSUME_TAC trace2_thm >>
  gvs [w2v_def],

  fs[p4_conc_finished_def],

  fs[v1model_ascope_of_conc_state_def, v1model_ascope_read_ext_obj_def] >>
  EVAL_TAC
 ]
]
QED

val _ = export_theory ();
