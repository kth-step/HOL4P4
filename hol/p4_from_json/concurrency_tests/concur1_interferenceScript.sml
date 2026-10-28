Theory concur1_interference
Ancestors
  p4_concurrent p4_v1model bitstring
Libs
  p4_testLib pairSyntax p4Syntax p4_v1modelLib p4_concurrency_testLib p4_concurrentSyntax

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
  arch_block_ffbl "traffic_manager";
  arch_block_pbl "MyEgress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyComputeChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyDeparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("MyParser",
   (pbl_type_parser,
    [("packet",d_none); ("hdr",d_out); ("meta",d_inout); ("standard_metadata",d_inout)],
    [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])], [],
    [("start",stmt_seq stmt_empty (stmt_trans (e_v (v_str "accept"))))], []));
  ("MyVerifyChecksum",
   (pbl_type_control, [("hdr",d_inout); ("meta",d_inout)],
    [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,[])], [], [], []));
  ("MyIngress",
   (pbl_type_control, [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
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
       [])],
     [(varn_name "tmp",tau_bit 16,NONE)], [],
     [("flowlet",[],"read_register",[]);
      ("new_flowlet",[],"write_register",[])]));
  ("MyEgress",
   (pbl_type_control, [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
    [("MyEgress",stmt_seq stmt_empty stmt_empty,[])], [], [], []));
  ("MyComputeChecksum",
   (pbl_type_control, [("hdr",d_inout); ("meta",d_inout)],
    [("MyComputeChecksum",stmt_seq stmt_empty stmt_empty,[])], [], [], []));
  ("MyDeparser",
   (pbl_type_control, [("packet",d_none); ("hdr",d_in)],
    [("MyDeparser",stmt_seq stmt_empty stmt_empty,[])], [], [], []))],
 [("postparser",ffblock_ff v1model_postparser);
  ("traffic_manager",ffblock_ff (v1model_traffic_manager random_oracle))],
 v1model_input_f random_oracle 1 (v_struct [],v_struct []),v1model_output_f,
 v1model_copyin_pbl,v1model_copyout_pbl,v1model_apply_table_f v1model_api_tdi,
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
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct random_oracle),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read random_oracle);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)])],
 [("NoAction",stmt_seq stmt_empty (stmt_ret (e_v v_bot)),[])],
 v1model_get_oracle_index,v1model_set_oracle_index,random_oracle):v1model_ascope actx``;

val concur1_astate =
 ``((0, (* Block index *)
     [([T], 1:num); ([F], 2)], (* Input list *)
     [], (* Output list *)
     (* 'a: *)
     1, (* Number of extern objects *)
     [(0, INR (v1model_v_ext_register [(fixwidth 16 [], 16)]))],
     (^v1model_init_v_map++["r", v_ext_ref 0]),
     [("flowlet",[]); ("new_flowlet",[])],
     0), (* End of 'a env *)
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
     [("flowlet",[]:(((e list -> bool) # num) # string # e list) list); ("new_flowlet",[])],
     0:num)
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
(* 29 steps to finishing first function *)
 val (_, ((i, _, in_out_list', _), _, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 29

(* 57 steps to finishing the entire program *)
 val (_, ((i, _, in_out_list', _), _, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 57

First witness from
  T1: 57 steps
  T2: 57 steps

Second witness from
  T1: 29 steps
  T2: 29 steps
  T1: 28 steps
  T2: 28 steps

 val (_, ((i, _, in_out_list', _), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "v1model" concur1_actx concur1_astate 57
*)

val init_conc_state = list_mk_pair[concur1_shared_s, concur1_t1_s, concur1_t2_s];

val trace1_thm =
 let
  val thm1 = get_trace_thread_n "v1model" concur1_actx init_conc_state 29 1
  val thm2 = get_trace_thread_next_n "v1model" concur1_actx thm1 29 2
  val thm3 = get_trace_thread_next_n "v1model" concur1_actx thm2 28 1
  val thm4 = get_trace_thread_next_n "v1model" concur1_actx thm3 28 2
 in
  thm4
 end;

val trace2_thm =
 let
  (* Call 1: to get_trace_thread_n *)
  val thm1 = get_trace_thread_n "v1model" concur1_actx init_conc_state 57 1

  (* Call 2: Should be to a new to get_trace_thread_next_n that continues from a theorem *)
  val thm2 = get_trace_thread_next_n "v1model" concur1_actx thm1 57 2
 in
  thm2
 end;

fun trace_final_state thm =
 let
  val (_, _, _, final) = dest_trace_path $ concl thm
  val (shared_s, thread_states) = pairSyntax.dest_pair final
  val (t1_s, t2_s) = pairSyntax.dest_pair thread_states
 in
  (shared_s, t1_s, t2_s)
 end;
val (shared_s', t1_s', t2_s') = trace_final_state trace1_thm;
val (shared_s'', _, _) = trace_final_state trace2_thm;

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
EXISTS_TAC “114:num” >>
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
