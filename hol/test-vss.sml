open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open pairSyntax wordsSyntax listSyntax bitstringSyntax numSyntax;
open p4Syntax;
open testLib;
open p4Lib p4_coreLib p4_vssLib p4_testLib;
open p4_exec_semTheory;
open p4_coreTheory;
open p4_vssTheory;
open blastLib;
open computeLib;
open alistTheory;

(* This file includes complete test runs of the VSS example in the P4 spec. *)

(*****************************)
(*   Architectural context   *)
(*****************************)
(**************)
(*   Parser   *)

(* start parser state *)
(* p.ethernet *)
val e_eth = ``e_acc (e_var (varn_name "p")) "ethernet"``;
val stmt_start_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [e_var (varn_name "b"); (^e_eth)])``;
(* p.ethernet.etherType *)
val e_eth_ty =
 ``e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType"``;
(* 0x0800 *)
val ether_ty_ok = mk_v_bitii (2048, 16);
val stmt_start_trans =
 ``stmt_trans (e_select (^e_eth_ty) ([((^ether_ty_ok), "parse_ipv4")]) "reject")``;

val start_body = mk_stmt_block (``[]:decl_list``, mk_stmt_seq_list [stmt_start_extract, stmt_start_trans]);


(* parse_ipv4 parser state *)
val e_ip = ``e_acc (e_var (varn_name "p")) "ip"``; (* p.ip *)
val stmt_parse_ipv4_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [e_var (varn_name "b"); (^e_ip)])``;

val e_ip_v = ``e_acc (^e_ip) "version"``; (* p.ip.version *)
val ip_v0_ok = mk_v_bitii (4, 4); (* Correct IP version number: 4w4 *)
val e_4w4 = mk_e_v ip_v0_ok; (* 4w4 (as expression) *)
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``; (* p.ip.version == 4w4 *)
val e_err_version = ``e_v (v_err "IPv4IncorrectVersion")``; (* error.IPv4IncorrectVersion *)
val stmt_parse_ipv4_verify1 = ``stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)``;

val e_ip_ihl = ``e_acc (^e_ip) "ihl"``; (* p.ip.ihl *)
val ip_ihl_ok = mk_v_bitii (5, 4); (* Correct IHL: 4w5 *)
val e_4w5 = mk_e_v ip_ihl_ok; (* 4w5 (as expression) *)
val e_ip_ihl_eq_4w5 = ``e_binop (^e_ip_ihl) binop_eq (^e_4w5)``; (* p.ip.ihl == 4w5 *)
val e_err_options = ``e_v (v_err "IPv4OptionsNotSupported")``; (* error.IPv4OptionsNotSupported *)
val stmt_parse_ipv4_verify2 = ``stmt_verify (^e_ip_ihl_eq_4w5) (^e_err_options)``;

val e_ck = mk_e_var_name "ck";
val stmt_parse_ipv4_clear =
 ``stmt_ass lval_null (e_call (funn_ext "Checksum16" "clear") [(^e_ck)])``;

val stmt_parse_ipv4_update =
 ``stmt_ass lval_null (e_call (funn_ext "Checksum16" "update") [(^e_ck); (^e_ip)])``;

val ck_ok = mk_v_bitii (0, 16); (* 16w0 *)
val e_16w0 = mk_e_v ck_ok; (* 16w0 (as expression) *)
val e_ck_eq_16w0 = ``e_binop (e_call (funn_ext "Checksum16" "get") [(^e_ck)]) binop_eq (^e_16w0)``; (* ck.get() == 16w0 *)
val e_err_checksum = ``e_v (v_err "IPv4ChecksumError")``; (* error.IPv4ChecksumError *)
val stmt_parse_ipv4_verify3 = ``stmt_verify (^e_ck_eq_16w0) (^e_err_checksum)``;

val stmt_parse_ipv4_trans = ``stmt_trans (e_v (v_str "accept"))``;

val parse_ipv4_body =
 mk_stmt_block (``[]:decl_list``,
  mk_stmt_seq_list [stmt_parse_ipv4_extract,
		    stmt_parse_ipv4_verify1,
		    stmt_parse_ipv4_verify2,
		    stmt_parse_ipv4_clear,
		    stmt_parse_ipv4_update,
		    stmt_parse_ipv4_verify3,
		    stmt_parse_ipv4_trans]);

val vss_parser_pmap = ``[("start", (^start_body));
                         ("parse_ipv4", (^parse_ipv4_body))]:pars_map``;

val vss_parser_decl_list = ``[(varn_name "ck", tau_ext)]``;
val vss_parser_inits =
 mk_stmt_seq_list [``stmt_ass lval_null (e_call (funn_inst "Checksum16") [(^e_ck)])``,
                   ``stmt_trans (e_v (v_str "start"))``];

val vss_parser_pbl =
 ``pblock_regular pbl_type_parser [("b", d_none); ("p", d_out)] [] (^vss_parser_decl_list) (^vss_parser_inits) (^vss_parser_pmap) []``;

val vss_parser_ab =
 ``arch_block_pbl "parser" [e_var (varn_name "b"); e_var (varn_name "parsedHeaders")]``;


(************)
(*   Pipe   *)

val ipv4_match_table =
 ``("ipv4_match", [mk_lpm], ("Drop_action",[]:e_list))``;
val check_ttl_table =
 ``("check_ttl", [mk_exact], ("NoAction", []:e_list))``;
val dmac_table = ``("dmac", [mk_exact], ("Drop_action",[]:e_list))``;
val smac_table =
 ``("smac", [mk_exact], ("Drop_action",[]:e_list))``;
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
 mk_e_binop (``(e_var (varn_name "parseError"))``, binop_neq_tm, ``(e_v (v_err "NoError"))``);
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
 mk_stmt_block (``[]:decl_list``,
  mk_stmt_seq_list [stmt_parseerror,
		    stmt_ipv4_match,
		    check_ttl_match,
		    dmac_match,
		    smac_match]);

val vss_pipe_decl_list = ``[(varn_name "nextHop", tau_bit 32)]``;

val vss_pipe_pbl = ``pblock_regular pbl_type_control [("headers", d_inout); ("parseError", d_in); ("inCtrl", d_in); ("outCtrl", d_out)] (^vss_pipe_bfunc_map) (^vss_pipe_decl_list) (^vss_pipe_body) [] (^vss_pipe_tblmap)``;

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

val vss_deparser_decl_list = ``[(varn_name "ck", tau_ext)]``;

val stmt_deparser_inits = ``stmt_ass lval_null (e_call (funn_inst "Checksum16") [(^e_ck)])``;

val vss_deparser_tblmap = ``[]:tbl_map``;
val vss_deparser_body =
 mk_stmt_block (``[]:decl_list``,
  mk_stmt_seq_list [stmt_deparser_inits,
                    stmt_deparser_emit,
		    stmt_deparser_cond,
		    stmt_deparser_emit2]);

val vss_deparser_pbl = ``pblock_regular pbl_type_control [("p", d_inout); ("b", d_none)] [] (^vss_deparser_decl_list) (^vss_deparser_body) [] (^vss_deparser_tblmap)``;

val vss_deparser_ab = ``arch_block_pbl "deparser" [e_var (varn_name "outputHeaders"); e_var (varn_name "b")]``;


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

val vss_func_map =
 ``(^core_func_map)``;

(* TODO: Make syntax functions *)
val vss_actx =
 ``(^(pairSyntax.list_mk_pair [``(^vss_ab_list):ab_list``,
                               ``(^vss_pblock_map):pblock_map``,
                               ``(^vss_ffblock_map):vss_ascope ffblock_map``,
                               ``(^vss_input_f):vss_ascope input_f``,
                               ``(^vss_output_f):vss_ascope output_f``,
                               ``(^vss_copyin_pbl):vss_ascope copyin_pbl``,
                               ``(^vss_copyout_pbl):vss_ascope copyout_pbl``,
                               ``(^vss_apply_table_f):vss_ascope apply_table_f``,
                               ``(^vss_ext_map):vss_ascope ext_map``,
                               ``(^vss_func_map):func_map``])):vss_ascope actx``;

(******************)
(*   Input data   *)
(******************)

(* HOL4 representation of the VSS P4 program:

vss_pblock_map
vss_ext_map
vss_func_map

*)

val input_port_ok = ``1``;

(* TODO: Make more realistic data *)
(* NOTE: Data in an IPv4 packet may be a minimum of 0 bytes, maximum of 65536 bytes *)
val input_data_ok = mk_list ([], bool);

(* The simplest IPV4 header that will be judged valid by the example *)
(* NOTE: This only assigns the version, IHL, total length, ttl and header checksum fields. *)
val input_ttl_ok = 1; (* NOTE: TTL 1 and 2 will be sent to CPU *)
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
                  [(``"version"``, mk_v_bitii (0, 4)),
                   (``"ihl"``, mk_v_bitii (0, 4)),
                   (``"diffserv"``, mk_v_bitii (0, 8)),
                   (``"totalLen"``, mk_v_bitii (0, 16)),
                   (``"identification"``, mk_v_bitii (0, 16)),
                   (``"flags"``, mk_v_bitii (0, 3)),
                   (``"fragOffset"``, mk_v_bitii (0, 13)),
                   (``"ttl"``, mk_v_bitii (0, 8)),
                   (``"protocol"``, mk_v_bitii (0, 8)),
                   (``"hdrChecksum"``, mk_v_bitii (0, 16)),
                   (``"srcAddr"``, mk_v_bitii (0, 32)),
                   (``"dstAddr"``, mk_v_bitii (0, 32))];

val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_bitii (0, 48)),
                   (``"srcAddr"``, mk_v_bitii (0, 48)),
                   (``"etherType"``, mk_v_bitii (0, 16))];

val parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];


val init_counter = ``2:num``;

val init_ext_obj_map = ``[(0, INL (core_v_ext_packet_in []));
                          (1, INL (core_v_ext_packet_out []))]:(num, v_ext) alist``;

(* All variables used in the architectural scope need to be declared *)
val init_v_map = ``[("inCtrl", v_struct [("inputPort", v_bit ([ARB; ARB; ARB; ARB],4))]);
                    ("outCtrl", v_struct [("outputPort", v_bit ([ARB; ARB; ARB; ARB],4))]);
                    ("b", v_ext_ref 0);
                    ("data_crc", v_ext_ref 1);
                    ("parsedHeaders", (^parsed_packet_struct_uninit));
                    ("headers", (^parsed_packet_struct_uninit));
                    ("outputHeaders", (^parsed_packet_struct_uninit));
                    ("parseError", v_err "NoError")]:(string, v) alist``;

(* TODO: Make syntax functions *)
val init_ascope = ``((^init_counter), (^init_ext_obj_map), (^init_v_map), []:vss_ctrl):vss_ascope``;

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

(* Single reduction: *)
EVAL ``arch_exec ((^vss_actx):vss_ascope actx) (^init_astate)``;

(* Multiple reductions: *)
(* In V1, this ended at 131 steps for TTL=1 in input *)
(* In V2, this ends at 210 steps for TTL=1 in input *)

(*
val nsteps = 76;
val astate = init_astate;
val actx = vss_actx;

*)

(* TODO: Make "exec arch block" function *)

fun eval_and_print_result actx astate nsteps =
 optionSyntax.dest_some $ rhs $ concl $ (fn thm => REWRITE_RULE [(SIMP_CONV (pure_ss++p4_v2w_ss) [] (rhs $ concl thm))] thm) $ EVAL ``arch_multi_exec ((^actx):vss_ascope actx) (^astate) ^(term_of_int nsteps)``;

(* Used for steps where architecture changes state *)
fun eval_and_print_aenv actx astate nsteps =
 el 1 $ snd $ strip_comb $ (eval_and_print_result actx astate nsteps);

(* Used for steps inside programmable blocks *)
fun eval_and_print_rest actx astate nsteps =
 el 2 $ snd $ strip_comb $ (eval_and_print_result actx astate nsteps);

fun dest_astate astate =
 let
  val (aenv, astate') = dest_pair astate
  val (g_scope_list, astate'') = dest_pair astate'
  val (arch_frame_list, status) = dest_pair astate''
 in
  (aenv, g_scope_list, arch_frame_list, status)
 end
;

fun dest_vss_aenv aenv =
 let
  val (i, aenv') = dest_pair aenv
  val (in_out_list, aenv'') = dest_pair aenv'
  val (in_out_list', ascope) = dest_pair aenv''
 in
  (i, in_out_list, in_out_list', ascope)
 end
;

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

(* arch_in: input read into b, data_crc and inCtrl *)
eval_and_print_aenv vss_actx init_astate 1;

(* arch_pbl_init: parser block arguments read into b and p *)
eval_and_print_rest vss_actx init_astate 2;

(*

val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step actx astate nsteps;

EVAL ``EL (^i) (^ab_list)``;

val x = ``"parser"``;
val el = ``[e_var (varn_name "b"); e_var (varn_name "parsedHeaders")]``;

EVAL ``ALOOKUP (^pblock_map) (^x)``;

val x_d_list = ``[("b",d_none); ("p",d_out)]``;
val pbl_type = ``pbl_type_parser``;

EVAL ``LENGTH (^el) = LENGTH (^x_d_list)``;

EVAL ``^copyout_pbl (^g_scope_list, ^scope, MAP SND ^x_d_list, MAP FST ^x_d_list, ^pbl_type, set_fin_status ^pbl_type ^status)``;

val [counter, ext_obj_map, v_map, ctrl] = spine_pair scope;

EVAL ``copyout (MAP FST ^x_d_list) (MAP SND ^x_d_list) [ [] ; [] ] [v_map_to_scope ^v_map] ^g_scope_list``;


(********** Nested exec sems ***********)

(* NOTE: For debugging frames_exec *)
val ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map), (scope, g_scope_list, frame_list, status)) = debug_frames_from_step actx astate nsteps;

(* NOTE: New g_scope_list from scopes_to_pass, use to debug stmt_exec *)
val g_scope_list' = optionSyntax.dest_some $ rhs $ concl $ EVAL ``scopes_to_pass (funn_name "start") ^func_map ^b_func_map ^g_scope_list``;

(* NOTE: For debugging stmt_exec *)

(* stmt_exec test: *)
val [ascope', g_scope_list', frame_list', status'] = spine_pair $ optionSyntax.dest_some $ rhs $ concl $ EVAL ``stmt_exec (^apply_table_f, ^ext_map, ^func_map, ^b_func_map, ^pars_map, ^tbl_map) (^scope, ^g_scope_list', ^frame_list, status_running)``

EVAL ``is_v (e_select
                (e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType")
                [(v_bit (w2v 2048w,16),"parse_ipv4")] "reject")``

EVAL ``e_exec (^apply_table_f, ^ext_map, ^func_map, ^b_func_map, ^pars_map, ^tbl_map) ^g_scope_list' [[]; []] (e_select
                (e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType")
                [(v_bit (w2v 2048w,16),"parse_ipv4")] "reject")``

EVAL ``is_v (e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType")``

EVAL ``e_exec (^apply_table_f, ^ext_map, ^func_map, ^b_func_map, ^pars_map, ^tbl_map) ^g_scope_list' [[]; []] (e_acc (e_acc (e_var (varn_name "p")) "ethernet") "etherType")``

EVAL ``is_v (e_acc (e_var (varn_name "p")) "ethernet")``

EVAL ``e_exec (^apply_table_f, ^ext_map, ^func_map, ^b_func_map, ^pars_map, ^tbl_map) ^g_scope_list' [[]; []] (e_acc (e_var (varn_name "p")) "ethernet")``

EVAL ``is_v (e_var (varn_name "p"))``



EVAL ``assign (^g_scope_list') v_bot (lval_varname (varn_star (funn_inst "Checksum16")))``


*)

(* After a number of arch_parser_exec steps: status set to status_pars_next (pars_next_pars_fin pars_finaccept) *)
eval_and_print_rest vss_actx init_astate 76;

(* arch_parser_ret: parseError and parsedHeaders copied out to arch scope *)
eval_and_print_aenv vss_actx init_astate 77;

(* arch_ffbl: Parser Runtime *)
eval_and_print_aenv vss_actx init_astate 71;

(* arch_control_init: arguments read into pbl-global scope, frame initialised *)
eval_and_print_rest vss_actx init_astate 72;

(* arch_control_exec: *)
eval_and_print_aenv vss_actx init_astate 146;

(* arch_control_ret: outCtrl written to arch scope *)
eval_and_print_aenv vss_actx init_astate 147;

(* arch_ffbl: pre-Deparser *)
eval_and_print_aenv vss_actx init_astate 148;

(* arch_control_init: arguments read into pbl-global scope, frame initialised *)
eval_and_print_rest vss_actx init_astate 149;

(* arch_control_exec *)
eval_and_print_rest vss_actx init_astate 208;

(* arch_control_ret: p written to arch scope *)
eval_and_print_aenv vss_actx init_astate 209;

(* arch_out: output read into output stream *)
eval_and_print_aenv vss_actx init_astate 210;

(* TODO: Fix up the below and add to CI *)
(*
(*******************************)
(*   Parser statement tests    *)

(* Erroneous IP version number: 4w3 *)
val ip_v0_bad = mk_v_bitii (3, 4);

val ipv4_header_uninit =
 mk_v_header_list F
                  [(``"version"``, mk_v_bitii (0, 4)),
                   (``"ihl"``, mk_v_bitii (0, 4)),
                   (``"diffserv"``, mk_v_bitii (0, 8)),
                   (``"totalLen"``, mk_v_bitii (0, 16)),
                   (``"identification"``, mk_v_bitii (0, 16)),
                   (``"flags"``, mk_v_bitii (0, 3)),
                   (``"fragOffset"``, mk_v_bitii (0, 13)),
                   (``"ttl"``, mk_v_bitii (0, 8)),
                   (``"protocol"``, mk_v_bitii (0, 8)),
                   (``"hdrChecksum"``, mk_v_bitii (0, 16)),
                   (``"srcAddr"``, mk_v_bitii (0, 32)),
                   (``"dstAddr"``, mk_v_bitii (0, 32))];

val ipv4_header_init =
 mk_v_header_list T
                  [(``"version"``, ip_v0_ok),
                   (``"ihl"``, mk_v_bitii (0, 4)),
                   (``"diffserv"``, mk_v_bitii (0, 8)),
                   (``"totalLen"``, mk_v_bitii (0, 16)),
                   (``"identification"``, mk_v_bitii (0, 16)),
                   (``"flags"``, mk_v_bitii (0, 3)),
                   (``"fragOffset"``, mk_v_bitii (0, 13)),
                   (``"ttl"``, mk_v_bitii (0, 8)),
                   (``"protocol"``, mk_v_bitii (0, 8)),
                   (``"hdrChecksum"``, mk_v_bitii (0, 16)),
                   (``"srcAddr"``, mk_v_bitii (0, 32)),
                   (``"dstAddr"``, mk_v_bitii (0, 32))];

val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_bitii (0, 48)),
                   (``"srcAddr"``, mk_v_bitii (0, 48)),
                   (``"etherType"``, mk_v_bitii (0, 16))];

val ethernet_header_init =
 mk_v_header_list T
                  [(``"dstAddr"``, mk_v_bitii (0, 48)),
                   (``"srcAddr"``, mk_v_bitii (0, 48)),
                   (``"etherType"``, ether_ty_ok)];

val parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];

val stacks_uninit_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_hdrs_ok)), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;
(* Stacks at parse_ipv4 state *)
val stacks_uninit_parse_ipv4_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_ipv4_hdr_ok)), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;

val stacks_init_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (^ipv4_header_init));
                                           ("ethernet", (^ethernet_header_init))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_ipv4_hdr_ok)), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;

val stacks_bad =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_header T [("version", (^ip_v0_bad))]))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;

(* ``:(string |-> (ext # (string # d) list))`` *)


val status = ``status_running``;

(* Test cases from the parser of the VSS example *)
(* TODO: Ensure no copy-paste, use terms defined earlier *)
val vss_parser_test_cases = [
  (*
  b.extract(p.ethernet);
  *)
  (``stmt_multi_exec (^ext_ctx) (^stmt_start_extract) (^stacks_uninit_ok) (^status) 20``, NONE),
  (*
  transition select(p.ethernet.etherType) {
      0x0800: parse_ipv4;
      // no default rule: all other packets rejected
  }
  *)
  (``stmt_multi_exec ctx (^stmt_start_trans) (^stacks_uninit_ok) (^status) 20``,
   SOME ``stmt_empty``),
  (*
  b.extract(p.ethernet);
  transition select(p.ethernet.etherType) {
      0x0800: parse_ipv4;
      // no default rule: all other packets rejected
  }
  *)
  (``stmt_multi_exec (^ext_ctx) (^start_body) (^stacks_uninit_ok) (^status) 20``,
   SOME ``stmt_empty``),
  (*
  p.ip.version == 4w4
  *)
  (``e_multi_exec ctx (^e_ip_v_eq_4w4) (^stacks_uninit_ok) (^status) 20``, NONE),
  (*
  verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
  *)
  (``stmt_multi_exec ctx (stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)) (^stacks_init_ok) (^status) 20``,
   SOME ``stmt_empty``),
  (``stmt_multi_exec ctx (stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)) (^stacks_bad) (^status) 20``,
   SOME ``stmt_empty``),
  (*
  b.extract(p.ip);
  verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
  verify(p.ip.ihl == 4w5, error.IPv4OptionsNotSupported);
  ck.clear();
  ck.update(p.ip);
  verify(ck.get() == 16w0, error.IPv4ChecksumError);
  transition accept;
  *)
  (``stmt_multi_exec (^ext_ctx) (^parse_ipv4_body) (^stacks_uninit_parse_ipv4_ok) (^status) 30``,
   SOME ``stmt_empty``)
];

fun eval_stmt_multi_exec tm =
 let
  val res_thm = EVAL tm
  val res_canon_thm = SIMP_RULE (pure_ss++p4_v2w_ss++FMAP_ss) [] res_thm
  val res_canon_tm = rhs $ concl res_canon_thm
  (* TODO: Return format? *)
(*
  val res_stmt_tm = fst $ dest_pair $ dest_some res_canon_tm
  val (res_stacks_tm, res_status_tm) = dest_pair $ snd $ dest_pair $ dest_some res_canon_tm
*)
 in
  (res_canon_tm, res_canon_thm)
 end
;

(* TODO: Do something here? *)
fun is_multi_exec_res_well_formed tm =
 true
;

(* Test parser VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_parser_test_cases;


(*************************************)
(*   Match-action statement tests    *)

val ipv4_header_postparser =
 mk_v_header_list F
                  [(``"version"``, mk_v_bitii (4, 4)),
                   (``"ihl"``, mk_v_bitii (5, 4)),
                   (``"diffserv"``, mk_v_bitii (0, 8)),
                   (``"totalLen"``, mk_v_bitii (0, 16)),
                   (``"identification"``, mk_v_bitii (0, 16)),
                   (``"flags"``, mk_v_bitii (0, 3)),
                   (``"fragOffset"``, mk_v_bitii (0, 13)),
                   (``"ttl"``, mk_v_bitii (0, 8)),
                   (``"protocol"``, mk_v_bitii (0, 8)),
                   (``"hdrChecksum"``, mk_v_bitii (65452, 16)),
                   (``"srcAddr"``, mk_v_bitii (0, 32)),
                   (``"dstAddr"``, mk_v_bitii (0, 32))];

val ethernet_header_postparser =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_bitii (0, 48)),
                   (``"srcAddr"``, mk_v_bitii (0, 48)),
                   (``"etherType"``, mk_v_bitii (0, 16))];

val parsed_packet_struct_postparser =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_postparser), (``"ip"``, ipv4_header_postparser)];

val in_control_struct_postparser =
 mk_v_struct_list [(``"inputPort"``, mk_v_bitii (0, 4))];
val out_control_struct_postparser =
 mk_v_struct_list [(``"outputPort"``, mk_v_bitii (0, 4))];

val stacks_postparser_ok =
 ``stacks_tup ([FEMPTY |+ ("headers", ((^parsed_packet_struct_postparser), NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("inCtrl", ((^in_control_struct_postparser), NONE)) |+
                          ("outCtrl", ((^out_control_struct_postparser), NONE)) |+
                          ("nextHop", v_bit (w2v (0w:word32), 32), NONE)]:scope list) ([]:call_stack)``;

val stacks_postparser_bad_error =
 ``stacks_tup ([FEMPTY |+ ("headers", ((^parsed_packet_struct_postparser), NONE)) |+
                          ("parseError", (v_err "PacketTooShort", NONE)) |+
                          ("inCtrl", ((^in_control_struct_postparser), NONE)) |+
                          ("outCtrl", ((^out_control_struct_postparser), NONE)) |+
                          ("nextHop", v_bit (w2v (0w:word32), 32), NONE)]:scope list) ([]:call_stack)``;


val toppipe_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, func_map, ``FEMPTY:pars_map``, t_map, ``(^ctrl):ctrl``];




(* Test cases from the match-action pipeline of the VSS example *)
(* TODO: Ensure no copy-paste, use terms defined earlier *)
val vss_matchaction_test_cases = [
  (*
  if (parseError != error.NoError) {
      Drop_action();  // invoke drop directly
      return;
  }
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_parseerror) (^stacks_postparser_ok) status_running 20``, NONE:term option),
  (* Note that the error case only takes steps up until the return statement *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_parseerror) (^stacks_postparser_bad_error) status_running 9``, NONE:term option),
  (*
  ipv4_match.apply(); // Match result will go into nextHop
  if (outCtrl.outputPort == DROP_PORT) return;
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_ipv4_match) (^stacks_postparser_ok) status_running 21``, NONE:term option),
  (*
  check_ttl.apply();
  if (outCtrl.outputPort == CPU_OUT_PORT) return;
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^check_ttl_match) (^stacks_postparser_ok) status_running 11``, NONE:term option),
  (*
  dmac.apply();
  if (outCtrl.outputPort == DROP_PORT) return;
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^dmac_match) (^stacks_postparser_ok) status_running 12``, NONE:term option),
  (*
  smac.apply();
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^smac_match) (^stacks_postparser_ok) status_running 7``, NONE:term option)
];

(* Test match-action pipeline VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_matchaction_test_cases;

(*********************************)
(*   Deparser statement tests    *)

val deparser_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, ``FEMPTY:func_map``, ``FEMPTY:pars_map``, t_map, ``(^ctrl)``];

(* NOTE: This does not include any effects from the match-action part *)
val stacks_postmatchaction_ok =
 ``stacks_tup ([FEMPTY |+ ("p", ((^parsed_packet_struct_postparser), NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_out []), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;

val vss_deparser_test_cases = [
  (*
  b.emit(p.ethernet);
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_deparser_emit) (^stacks_init_ok) status_running 7``, NONE:term option),
  (*
  if (p.ip.isValid()) {
      ck.clear();              // prepare checksum unit
      p.ip.hdrChecksum = 16w0; // clear checksum
      ck.update(p.ip);         // compute new checksum.
      p.ip.hdrChecksum = ck.get();
  }
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_deparser_cond) (^stacks_init_ok) status_running 14``, NONE:term option),
  (*
  b.emit(p.ip);
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_deparser_emit2) (^stacks_init_ok) status_running 7``, NONE:term option)
];

(* Test match-action pipeline VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_deparser_test_cases;
*)
