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

(* This file includes complete test runs of the VSS example in the P4 spec. *)

(*****************************)
(*   Architectural context   *)
(*****************************)
(**************)
(*   Parser   *)

(* start parser state *)
(* p.ethernet *)
val e_eth = ``e_acc (e_var (varn_name "p")) (e_v (v_str "ethernet"))``;
val stmt_start_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [(e_var (varn_name "b")); (^e_eth)])``;
(* p.ethernet.etherType *)
val e_eth_ty =
 ``(e_acc (e_acc (e_var (varn_name "p")) (e_v (v_str "ethernet"))) (e_v (v_str "etherType")))``;
(* 0x0800 *)
val ether_ty_ok = mk_v_bitii (2048, 16);
val stmt_start_trans =
 ``stmt_trans (e_select (^e_eth_ty) ([((^ether_ty_ok), "parse_ipv4")]) "reject")``;

val start_body = mk_stmt_block $ mk_stmt_seq_list [stmt_start_extract, stmt_start_trans];


(* parse_ipv4 parser state *)
val e_ip = ``e_acc (e_var (varn_name "p")) (e_v (v_str "ip"))``; (* p.ip *)
val stmt_parse_ipv4_extract =
 ``stmt_ass lval_null (e_call (funn_ext "packet_in" "extract") [(e_var (varn_name "b")); (^e_ip)])``;

val e_ip_v = ``(e_acc (^e_ip) (e_v (v_str "version")))``; (* p.ip.version *)
val ip_v0_ok = mk_v_bitii (4, 4); (* Correct IP version number: 4w4 *)
val e_4w4 = mk_e_v ip_v0_ok; (* 4w4 (as expression) *)
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``; (* p.ip.version == 4w4 *)
val e_err_version = ``e_v (v_err "IPv4IncorrectVersion")``; (* error.IPv4IncorrectVersion *)
val stmt_parse_ipv4_verify1 = ``stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)``;

val e_ip_ihl = ``(e_acc (^e_ip) (e_v (v_str "ihl")))``; (* p.ip.ihl *)
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
 mk_stmt_block $ 
 mk_stmt_seq_list [stmt_parse_ipv4_extract,
		   stmt_parse_ipv4_verify1,
		   stmt_parse_ipv4_verify2,
		   stmt_parse_ipv4_clear,
		   stmt_parse_ipv4_update,
		   stmt_parse_ipv4_verify3,
		   stmt_parse_ipv4_trans];

val vss_parser_pmap = ``FEMPTY |+ ("start", (^start_body))
                               |+ ("parse_ipv4", (^parse_ipv4_body))``;

val vss_parser_decls =
 ``stmt_declare t_ext "ck" (SOME (e_call (funn_inst "Checksum16") []))``;

val vss_parser_pbl =
 ``pblock_parser [("b", d_none); ("p", d_out)] (^vss_parser_decls) (^vss_parser_pmap)``;

val vss_parser_ab =
 ``arch_block_pbl "parser" [e_var (varn_name "b"); e_var (varn_name "parsedHeaders")]``;


(************)
(*   Pipe   *)

val ipv4_match_table =
 ``("ipv4_match", (e_acc (e_acc (e_var (varn_name "headers")) (e_v (v_str "ip"))) (e_v (v_str "dstAddr")), mk_lpm))``;
val check_ttl_table =
 ``("check_ttl", (e_acc (e_acc (e_var (varn_name "headers")) (e_v (v_str "ip"))) (e_v (v_str "ttl")), mk_exact))``;
val dmac_table = ``("dmac", (e_var (varn_name "nextHop"), mk_exact))``;
val smac_table =
 ``("smac", (e_acc (e_var (varn_name "outCtrl")) (e_var (varn_name "outputPort")), mk_exact))``;
val vss_pipe_tblmap = ``FEMPTY |+ (^ipv4_match_table)
                               |+ (^check_ttl_table)
                               |+ (^dmac_table)
                               |+ (^smac_table)``;

(* Body *)
val e_parseerror_cond =
 mk_e_binop (``(e_var (varn_name "parseError"))``, binop_neq_tm, ``(e_v (v_err "NoError"))``);
val stmt_parseerror_then =
 mk_stmt_seq (mk_stmt_ass (lval_null_tm, mk_e_call (``funn_name "Drop_action"``, ``[]:e list``)) , mk_stmt_ret ``e_v v_bot``);

val stmt_parseerror = mk_stmt_cond (e_parseerror_cond, stmt_parseerror_then, stmt_empty_tm);

val e_ipv4_match_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) (e_v (v_str "outputPort")))``, binop_eq_tm, mk_e_var_name "DROP_PORT");
val stmt_ipv4_match =
 mk_stmt_seq (mk_stmt_app (``"ipv4_match"``, ``e_v v_bot``), mk_stmt_cond (e_ipv4_match_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_check_ttl_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) (e_v (v_str "outputPort")))``, binop_eq_tm, mk_e_var_name "CPU_OUT_PORT");
val check_ttl_match =
 mk_stmt_seq (mk_stmt_app (``"check_ttl"``, ``e_acc (e_acc (e_var (varn_name "headers")) (e_v (v_str "ip"))) (e_v (v_str "ttl"))``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_dmac_cond =
 mk_e_binop (``(e_acc (e_var (varn_name "outCtrl")) (e_v (v_str "outputPort")))``, binop_eq_tm, mk_e_var_name "DROP_PORT");
val dmac_match =
 mk_stmt_seq (mk_stmt_app (``"dmac"``, ``e_v v_bot``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val smac_match = mk_stmt_app (``"smac"``, ``e_v v_bot``);

val vss_pipe_body =
 mk_stmt_block $ 
 mk_stmt_seq_list [stmt_parseerror,
		   stmt_ipv4_match,
		   check_ttl_match,
		   dmac_match,
		   smac_match];

val vss_pipe_decls = ``stmt_declare (t_base bt_bit) "nextHop" NONE``;

val vss_pipe_pbl = ``pblock_control [("headers", d_inout); ("parseError", d_in); ("inCtrl", d_in); ("outCtrl", d_out)] (^vss_pipe_decls) (^vss_pipe_body) (^vss_pipe_tblmap)``;

val vss_pipe_ab = ``arch_block_pbl "pipe" [e_var (varn_name "headers"); e_var (varn_name "parseError"); e_var (varn_name "inCtrl"); e_var (varn_name "outCtrl")]``;


(****************)
(*   Deparser   *)

val stmt_deparser_emit =
 ``stmt_ass lval_null (e_call (funn_ext "packet_out" "emit") [e_var (varn_name "b"); (^e_eth)])``;

(* p.ip.hdrChecksum *)
val lval_ip_ck = mk_lval_field (mk_lval_field (mk_lval_varname "p", "ip"), "hdrChecksum");
val lval_p_ip = mk_lval_field (mk_lval_varname "p", "ip");
val e_p_ip = mk_e_acc (mk_e_var_name "p", mk_e_v $ mk_v_str "ip");

val stmt_deparser_cond =
 ``stmt_cond (e_call (funn_ext "header" "isValid") [(^e_p_ip)])
	     (^(mk_stmt_seq_list [(mk_stmt_ass (lval_null_tm, mk_e_ext_call_list ("Checksum16", "clear", ([e_ck]:term list)))),
				  mk_stmt_ass (lval_ip_ck, mk_e_v $ mk_v_bitii (0, 16)),
				  mk_stmt_ass (lval_null_tm, mk_e_ext_call_list ("Checksum16", "update", ([e_ck, e_ip]:term list))),
				  mk_stmt_ass (lval_ip_ck, mk_e_ext_call_list ("Checksum16", "get", ([e_ck]:term list)))]))
				  stmt_empty``;

val stmt_deparser_emit2 = ``stmt_ass lval_null (e_call (funn_ext "packet_out" "emit") [e_var (varn_name "b"); (^e_ip)])``;

(* TODO: Is this table map correct? *)
val vss_deparser_tblmap = ``FEMPTY:tbl_map``;
val vss_deparser_body =
 mk_stmt_block $ 
 mk_stmt_seq_list [stmt_deparser_emit,
		   stmt_deparser_cond,
		   stmt_deparser_emit2];

val vss_deparser_decls =
 ``stmt_declare t_ext "ck" (SOME (e_call (funn_inst "Checksum16") []))``;

val vss_deparser_pbl = ``pblock_control [("p", d_inout); ("b", d_none)] (^vss_deparser_decls) (^vss_deparser_body) (^vss_deparser_tblmap)``;

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
val vss_pblock_map = ``FEMPTY |+ ("parser", (^vss_parser_pbl))
                              |+ ("pipe", (^vss_pipe_pbl))
                              |+ ("deparser", (^vss_deparser_pbl))``;

val vss_ty_map = ``FEMPTY:ty_map``;

val e_outport = mk_lval_field (mk_lval_varname "outCtrl", "outputPort");
val drop_action_fun = ``("Drop_action", stmt_seq (stmt_ass (^e_outport) (e_var (varn_name "DROP_PORT"))) (stmt_ret (e_v v_bot)), []:(string # d) list)``;
val lval_headers_ip_ttl = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ip"), "ttl");
val e_headers_ip_ttl = mk_e_acc (mk_e_acc (mk_e_var_name "headers", mk_e_v $ mk_v_str "ip"), mk_e_v $ mk_v_str "ttl");
val set_nhop_fun = ``("Set_nhop", (^(mk_stmt_seq_list [(mk_stmt_ass (mk_lval_varname "nextHop", mk_e_var_name "ipv4_dest")),
                                                       (mk_stmt_ass (lval_headers_ip_ttl, mk_e_binop (e_headers_ip_ttl, binop_sub_tm, mk_e_v (mk_v_bitii (1, 8))))),
                                                       
                                                       (mk_stmt_ass (mk_lval_field (mk_lval_varname "outCtrl", "outputPort"), mk_e_var_name "port")), 
                                                       mk_stmt_ret (mk_e_v v_bot_tm)])), [("ipv4_dest", d_none); ("port", d_none)]:(string # d) list)``;
val send_to_cpu_fun = ``("Send_to_cpu", stmt_seq (stmt_ass (^e_outport) (e_var (varn_name "CPU_OUT_PORT"))) (stmt_ret (e_v v_bot)), []:(string # d) list)``;
val lval_ethdst = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "dstAddr");
val set_dmac_fun = ``("Set_dmac", stmt_seq (stmt_ass (^lval_ethdst) (e_var (varn_name "dmac"))) (stmt_ret (e_v v_bot)), [("dmac", d_none)]:(string # d) list)``;
val lval_ethsrc = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "srcAddr");
val set_smac_fun = ``("Set_smac", stmt_seq (stmt_ass (^lval_ethsrc) (e_var (varn_name "smac"))) (stmt_ret (e_v v_bot)), [("smac", d_none)]:(string # d) list)``;
val vss_func_map =
 ``(^core_func_map) |+ (^drop_action_fun)
                    |+ (^set_nhop_fun)
                    |+ (^send_to_cpu_fun)
                    |+ (^set_dmac_fun)
                    |+ (^set_smac_fun)``;

val vss_actx = pairSyntax.list_mk_pair [vss_ab_list, vss_pblock_map, vss_ffblock_map, vss_input_f, vss_output_f, vss_ty_map, vss_ext_map, vss_func_map];

(******************)
(*   Input data   *)
(******************)

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

(* TODO: Initialise these with "ARB" instead? *)
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


(* All variables used at architectural level need to be declared *)
val init_scope_ok = ``(FEMPTY |+ (varn_name "inCtrl", (v_struct [("inputPort", v_bit ([ARB; ARB; ARB; ARB],4))], NONE))
                              |+ (varn_name "outCtrl", (v_struct [("outputPort", v_bit ([ARB; ARB; ARB; ARB],4))], NONE))
                              |+ (varn_name "b", (v_ext (ext_obj_in []), NONE))
                              |+ (varn_name "data_crc", (v_ext (ext_obj_out []), NONE))
                              |+ (varn_name "parsedHeaders", ((^parsed_packet_struct_uninit), NONE))
                              |+ (varn_name "headers", ((^parsed_packet_struct_uninit), NONE))
                              |+ (varn_name "outputHeaders", ((^parsed_packet_struct_uninit), NONE))
                              |+ (varn_name "parseError", (v_err "NoError", NONE))):scope``;

(* Architectural block index is 0,
 * programmable block in-progress flag set to false,
 * Input list contains only some OK input at port 1,
 * Output list is empty,
 * Scope is empty. *)
val init_aenv = pairSyntax.list_mk_pair [``0``, F, init_inlist_ok, init_outlist_ok, ``(^init_scope_ok)``];

(* Note: this is a really primitive representation of what
 * the control plane configuration might be *)
Definition ctrl_check_ttl:
 (ctrl_check_ttl (v, mk:mk) =
  case v of
  | (v_bit (bl,n)) =>
   if (v2n bl) > 0
   then SOME ("NoAction", [])
   else SOME ("Send_to_cpu", [])
  | _ => NONE
 )
End

val ctrl =
 ``\(table_name, v, (mk:mk)).
   if table_name = "ipv4_match"
   then SOME ("Set_nhop",
              [e_v (v_bit (w2v (42w:word32),32));
               e_v (v_bit (w2v (2w:word4),4))])
   else if table_name = "check_ttl"
   then ctrl_check_ttl (v, mk)
   else if table_name = "dmac"
   then SOME ("Set_dmac",
              [e_v (v_bit (w2v (2525w:word48),48))])
   else if table_name = "smac"
   then SOME ("Set_smac",
              [e_v (v_bit (w2v (2525w:word48),48))])
   else NONE``;

val init_astate =
 pairSyntax.list_mk_pair [init_aenv,
                          listSyntax.mk_list ([vss_init_global_scope], scope_ty),
                          arch_frame_list_empty_tm, ctrl, status_running_tm];

(*******************************************)
(*   Architecture-level semantics tests    *)

(* Single reduction: *)
EVAL ``arch_exec ((^vss_actx):actx) (^init_astate)``;

(* Multiple reductions: *)
(* TODO: Fix p4_v2w_ss, why doesn't this work? *)
(* In V1, this ended at 131 steps for TTL=1 in input *)
(* In V2, this ends at 217 steps for TTL=1 in input *)
el 1 $ snd $ strip_comb $ optionSyntax.dest_some $ rhs $ concl $ (SIMP_RULE (pure_ss++p4_v2w_ss++FMAP_ss) []) $ EVAL ``arch_multi_exec ((^vss_actx):actx) (^init_astate) 217``;

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
