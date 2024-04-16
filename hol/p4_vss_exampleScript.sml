open HolKernel boolLib Parse bossLib;

open p4Theory p4_vssTheory;
open pairSyntax listSyntax p4Syntax;

open p4_vssLib;

val _ = new_theory "p4_vss_example";

(* This file contains the VSS example program. Specifically, it saves a theorem
 * that contains the architectural context of the program. *)

(**************)
(*   Parser   *)

(* start parser state *)

val e_eth = ``e_acc (e_var (varn_name "p")) "ethernet"``;
val stmt_start_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [e_var (varn_name "b"); (^e_eth)])``;

val e_eth_ty =
 ``e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType"``;
val ether_ty_ok = mk_v_bitii (2048, 16);
val stmt_start_trans =
 ``stmt_trans (e_select (e_struct [("", ^e_eth_ty)]) ([([(s_sing ^ether_ty_ok)], "parse_ipv4")]) "reject")``;

val start_body = mk_stmt_block (``[]:t_scope``, mk_stmt_seq_list [stmt_start_extract, stmt_start_trans]);


(* parse_ipv4 parser state *)
val e_ip = ``e_acc (e_var (varn_name "p")) "ip"``; (* p.ip *)
val stmt_parse_ipv4_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [e_var (varn_name "b"); (^e_ip)])``;

val e_ip_v = ``e_acc (^e_ip) "version"``; (* p.ip.version *)
val ip_v0_ok = mk_v_bitii (4, 4); (* Correct IP version number: 4w4 *)
val e_4w4 = mk_e_v ip_v0_ok; (* 4w4 (as expression) *)
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``; (* p.ip.version == 4w4 *)
val e_err_version = ``e_v ^(mk_v_bitii (8, 32))``; (* error.IPv4IncorrectVersion *)
val stmt_parse_ipv4_verify1 = ``stmt_ass lval_null (e_call (funn_ext "" "verify") [(^e_ip_v_eq_4w4); (^e_err_version)])``;

val e_ip_ihl = ``e_acc (^e_ip) "ihl"``; (* p.ip.ihl *)
val ip_ihl_ok = mk_v_bitii (5, 4); (* Correct IHL: 4w5 *)
val e_4w5 = mk_e_v ip_ihl_ok; (* 4w5 (as expression) *)
val e_ip_ihl_eq_4w5 = ``e_binop (^e_ip_ihl) binop_eq (^e_4w5)``; (* p.ip.ihl == 4w5 *)
val e_err_options = ``e_v ^(mk_v_bitii (7, 32))``; (* error.IPv4OptionsNotSupported *)
val stmt_parse_ipv4_verify2 = ``stmt_ass lval_null (e_call (funn_ext "" "verify") [(^e_ip_ihl_eq_4w5); (^e_err_options)])``;

val e_ck = mk_e_var_name "ck";
val stmt_parse_ipv4_clear =
 ``stmt_ass lval_null (e_call (funn_ext "Checksum16" "clear") [(^e_ck)])``;

val stmt_parse_ipv4_update =
 ``stmt_ass lval_null (e_call (funn_ext "Checksum16" "update") [(^e_ck); (^e_ip)])``;

val ck_ok = mk_v_bitii (0, 16); (* 16w0 *)
val e_16w0 = mk_e_v ck_ok; (* 16w0 (as expression) *)
val e_ck_eq_16w0 = ``e_binop (e_call (funn_ext "Checksum16" "get") [(^e_ck)]) binop_eq (^e_16w0)``; (* ck.get() == 16w0 *)
val e_err_checksum = ``e_v ^(mk_v_bitii (9, 32))``; (* error.IPv4ChecksumError *)
val stmt_parse_ipv4_verify3 = ``stmt_ass lval_null (e_call (funn_ext "" "verify") [(^e_ck_eq_16w0); (^e_err_checksum)])``;

val stmt_parse_ipv4_trans = ``stmt_trans (e_v (v_str "accept"))``;

val parse_ipv4_body =
 mk_stmt_block (``[]:t_scope``,
  mk_stmt_seq_list [stmt_parse_ipv4_extract,
		    stmt_parse_ipv4_verify1,
		    stmt_parse_ipv4_verify2,
		    stmt_parse_ipv4_clear,
		    stmt_parse_ipv4_update,
		    stmt_parse_ipv4_verify3,
		    stmt_parse_ipv4_trans]);

val vss_parser_pmap = ``[("start", (^start_body));
                         ("parse_ipv4", (^parse_ipv4_body))]:pars_map``;

val vss_parser_decl_list = ``[(varn_name "ck", tau_ext, NONE)]:t_scope``;
val vss_parser_inits =
 mk_stmt_seq_list [``stmt_ass lval_null (e_call (funn_inst "Checksum16") [(^e_ck)])``,
                   ``stmt_trans (e_v (v_str "start"))``];

val vss_parser_pbl =
 ``(pbl_type_parser, [("b", d_none); ("p", d_out)], [("parser", (^vss_parser_inits, []))], (^vss_parser_decl_list), (^vss_parser_pmap), []):pblock``;

val vss_parser_ab =
 ``arch_block_pbl "parser" [e_var (varn_name "b_in"); e_var (varn_name "parsedHeaders")]``;


(************)
(*   Pipe   *)

val ipv4_match_table =
 ``("ipv4_match", [mk_lpm], ["Drop_action"; "Set_nhop"], ("Drop_action",[]:e_list))``;
val check_ttl_table =
 ``("check_ttl", [mk_exact], ["Send_to_cpu"; "NoAction"], ("NoAction", []:e_list))``;
val dmac_table = ``("dmac", [mk_exact], ["Drop_action"; "Set_dmac"], ("Drop_action",[]:e_list))``;
val smac_table =
 ``("smac", [mk_exact], ["Drop_action"; "Set_smac"], ("Drop_action",[]:e_list))``;
val vss_pipe_tblmap = ``[(^ipv4_match_table);
                         (^check_ttl_table);
                         (^dmac_table);
                         (^smac_table)]:tbl_map``;

val e_outport = mk_lval_field (mk_lval_varname "outCtrl", "outputPort");
val drop_action_fun = ``("Drop_action", stmt_seq (stmt_ass (^e_outport) (e_var (varn_name "DROP_PORT"))) (stmt_ret (e_v v_bot)), []:(string # d) list)``;
val lval_headers_ip_ttl = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ip"), "ttl");
val e_headers_ip_ttl = mk_e_acc (mk_e_acc (mk_e_var_name "headers", "ip"), "ttl");
val set_nhop_fun = ``("Set_nhop", (^(mk_stmt_seq_list [(mk_stmt_ass (mk_lval_varname "nextHop", mk_e_var_name "ipv4_dest")),
                                                       (mk_stmt_ass (lval_headers_ip_ttl, mk_e_binop (e_headers_ip_ttl, binop_sub_tm, mk_e_v (mk_v_bitii (1, 8))))),
                                                       (mk_stmt_ass (mk_lval_field (mk_lval_varname "outCtrl", "outputPort"), mk_e_var_name "port")), 
                                                       mk_stmt_ret (mk_e_v v_bot_tm)])), [("ipv4_dest", d_none); ("port", d_none)]:(string # d) list)``;
val send_to_cpu_fun = ``("Send_to_cpu", stmt_seq (stmt_ass (^e_outport) (e_var (varn_name "CPU_OUT_PORT"))) (stmt_ret (e_v v_bot)), []:(string # d) list)``;
val lval_ethdst = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "dstAddr");
val set_dmac_fun = ``("Set_dmac", stmt_seq (stmt_ass (^lval_ethdst) (e_var (varn_name "dmac"))) (stmt_ret (e_v v_bot)), [("dmac", d_none)]:(string # d) list)``;
val lval_ethsrc = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "srcAddr");
val set_smac_fun = ``("Set_smac", stmt_seq (stmt_ass (^lval_ethsrc) (e_var (varn_name "smac"))) (stmt_ret (e_v v_bot)), [("smac", d_none)]:(string # d) list)``;
val vss_pipe_bfunc_map =
 ``[(^drop_action_fun);
    (^set_nhop_fun);
    (^send_to_cpu_fun);
    (^set_dmac_fun);
    (^set_smac_fun)]``;

(* Body *)
val e_parseerror_cond =
 mk_e_binop (``(e_var (varn_name "parseError"))``, binop_neq_tm, ``(e_v ^(mk_v_bitii (0, 32)))``);
val stmt_parseerror_then =
 mk_stmt_seq (mk_stmt_ass (lval_null_tm, mk_e_call (``funn_name "Drop_action"``, ``[]:e list``)) , mk_stmt_ret ``e_v v_bot``);

val stmt_parseerror = mk_stmt_cond (e_parseerror_cond, stmt_parseerror_then, stmt_empty_tm);

val e_ipv4_match_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) "outputPort")``, binop_eq_tm, mk_e_var_name "DROP_PORT");
val stmt_ipv4_match =
 mk_stmt_seq (mk_stmt_app (``"ipv4_match"``, ``[e_acc (e_acc (e_var (varn_name "headers")) "ip") "dstAddr"]``), mk_stmt_cond (e_ipv4_match_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_check_ttl_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) "outputPort")``, binop_eq_tm, mk_e_var_name "CPU_OUT_PORT");
val check_ttl_match =
 mk_stmt_seq (mk_stmt_app (``"check_ttl"``, ``[e_acc (e_acc (e_var (varn_name "headers")) "ip") "ttl"]``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_dmac_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) "outputPort")``, binop_eq_tm, mk_e_var_name "DROP_PORT");
val dmac_match =
 mk_stmt_seq (mk_stmt_app (``"dmac"``, ``[e_var (varn_name "nextHop")]``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val smac_match = mk_stmt_app (``"smac"``, ``[e_acc (e_var (varn_name "outCtrl")) "outputPort"]``);

val vss_pipe_body =
 mk_stmt_block (``[]:t_scope``,
  mk_stmt_seq_list [stmt_parseerror,
		    stmt_ipv4_match,
		    check_ttl_match,
		    dmac_match,
		    smac_match]);

val vss_pipe_decl_list = ``[(varn_name "nextHop", tau_bit 32, NONE)]:t_scope``;

val vss_pipe_pbl = ``(pbl_type_control, [("headers", d_inout); ("parseError", d_in); ("inCtrl", d_in); ("outCtrl", d_out)], (("pipe", (^vss_pipe_body, []))::(^vss_pipe_bfunc_map)), (^vss_pipe_decl_list), [], (^vss_pipe_tblmap)):pblock``;

val vss_pipe_ab = ``arch_block_pbl "pipe" [e_var (varn_name "headers"); e_var (varn_name "parseError"); e_var (varn_name "inCtrl"); e_var (varn_name "outCtrl")]``;


(****************)
(*   Deparser   *)

val stmt_deparser_emit =
 ``stmt_ass lval_null (e_call (funn_ext "packet_out" "emit") [e_var (varn_name "b"); (^e_eth)])``;

(* p.ip.hdrChecksum *)
val lval_ip_ck = mk_lval_field (mk_lval_field (mk_lval_varname "p", "ip"), "hdrChecksum");
val lval_p_ip = mk_lval_field (mk_lval_varname "p", "ip");
val e_p_ip = mk_e_acc (mk_e_var_name "p", "ip");

val stmt_deparser_cond =
 ``stmt_cond (e_call (funn_ext "header" "isValid") [(^e_p_ip)])
	     (^(mk_stmt_seq_list [(mk_stmt_ass (lval_null_tm, mk_e_ext_call_list ("Checksum16", "clear", ([e_ck]:term list)))),
				  mk_stmt_ass (lval_ip_ck, mk_e_v $ mk_v_bitii (0, 16)),
				  mk_stmt_ass (lval_null_tm, mk_e_ext_call_list ("Checksum16", "update", ([e_ck, e_ip]:term list))),
				  mk_stmt_ass (lval_ip_ck, mk_e_ext_call_list ("Checksum16", "get", ([e_ck]:term list)))]))
				  stmt_empty``;

val stmt_deparser_emit2 = ``stmt_ass lval_null (e_call (funn_ext "packet_out" "emit") [e_var (varn_name "b"); (^e_ip)])``;

val vss_deparser_decl_list = ``[(varn_name "ck", tau_ext, NONE)]:t_scope``;

val stmt_deparser_inits = ``stmt_ass lval_null (e_call (funn_inst "Checksum16") [(^e_ck)])``;

val vss_deparser_tblmap = ``[]:tbl_map``;
val vss_deparser_body =
 mk_stmt_block (``[]:t_scope``,
  mk_stmt_seq_list [stmt_deparser_inits,
                    stmt_deparser_emit,
		    stmt_deparser_cond,
		    stmt_deparser_emit2]);

val vss_deparser_pbl = ``(pbl_type_control, [("p", d_inout); ("b", d_none)], [("deparser", (^vss_deparser_body, []))], (^vss_deparser_decl_list), [], (^vss_deparser_tblmap)):pblock``;

val vss_deparser_ab = ``arch_block_pbl "deparser" [e_var (varn_name "outputHeaders"); e_var (varn_name "b_out")]``;


(**********************)
(*   Whole pipeline   *)

val vss_ab_list =
  mk_list ([``arch_block_inp``,  (* Arbiter built-in *)
            vss_parser_ab,  (* Parser *)
            ``arch_block_ffbl "parser_runtime"``, (* Parser Runtime *)
            vss_pipe_ab,  (* Match-Action Pipeline *)
            ``arch_block_ffbl "pre_deparser"``, (* pre-Deparser *)
            vss_deparser_ab,  (* Deparser *)
            ``arch_block_out`` (* Demux/queue built-in *)], ``:arch_block``);

(* Architectural context components: *)
val vss_pblock_map = ``[("parser", (^vss_parser_pbl));
                        ("pipe", (^vss_pipe_pbl));
                        ("deparser", (^vss_deparser_pbl))]``;

(* TODO: Make syntax functions *)
val vss_actx =
 ``(^(list_mk_pair [``(^vss_ab_list):ab_list``,
                    ``(^vss_pblock_map):pblock_map``,
                    ``(^vss_ffblock_map):vss_ascope ffblock_map``,
                    ``(^vss_input_f):vss_ascope input_f``,
                    ``(^vss_output_f):vss_ascope output_f``,
                    ``(^vss_copyin_pbl):vss_ascope copyin_pbl``,
                    ``(^vss_copyout_pbl):vss_ascope copyout_pbl``,
                    ``(^vss_apply_table_f):vss_ascope apply_table_f``,
                    ``(^vss_ext_map):vss_ascope ext_map``,
                    ``(^vss_func_map):func_map``])):vss_ascope actx``;

Definition p4_vss_actx_def:
  p4_vss_actx = ^vss_actx
End

val _ = export_theory ();
