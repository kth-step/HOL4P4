open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open pairSyntax wordsSyntax;
open p4Syntax;
open testLib;
open p4Lib;
open p4_exec_semTheory;
open p4_coreTheory;
open p4_vssTheory;
open blastLib;

(*************************************************************************************)
(* This file includes some tests run on fragments of the VSS example in the P4 spec. *)
(*************************************************************************************)

(*************************)
(*   From VSS Example    *)
(*************************)

(*********************)
(*   Parser tests    *)

(* 0x0800 *)
val ether_ty_ok = mk_v_bitii (2048, 16);

(* Checksum - computed from other IPv4 header fields *)
val checksum_ok = ``v_bit (w2v (-84w:word16),16)``;

(* 4w4 *)
val ip_v0_ok = mk_v_bitii (4, 4);
(* 4w3 *)
val ip_v0_bad = mk_v_bitii (3, 4);
(* 4w5 *)
val ip_ihl_ok = mk_v_bitii (5, 4);
(* 16w0 *)
val ck_ok = mk_v_bitii (0, 16);

(* TODO: Use syntax functions *)
(* p.ethernet *)
val e_eth = ``e_acc (e_var "p") (e_var "ethernet")``;
(* p.ip *)
val e_ip = ``e_acc (e_var "p") (e_var "ip")``;
(* p.ip.version *)
val e_ip_v = ``(e_acc (^e_ip) (e_var "version"))``;
(* p.ip.ihl *)
val e_ip_ihl = ``(e_acc (^e_ip) (e_var "ihl"))``;
(* 4w4 (as expression) *)
val e_4w4 = mk_e_v ip_v0_ok;
(* 4w5 (as expression) *)
val e_4w5 = mk_e_v ip_ihl_ok;
(* 16w0 (as expression) *)
val e_16w0 = mk_e_v ck_ok;
(* p.ip.version == 4w4 *)
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``;
(* p.ip.ihl == 4w5 *)
val e_ip_ihl_eq_4w5 = ``e_binop (^e_ip_ihl) binop_eq (^e_4w5)``;
(* ck.get() == 16w0 *)
val e_ck_eq_16w0 = ``e_binop (e_ext_call (lval_varname "ck") "get" []) binop_eq (^e_16w0)``;

(* error.IPv4IncorrectVersion *)
val e_err_version = ``e_v (v_err "IPv4IncorrectVersion")``;
(* error.IPv4OptionsNotSupported *)
val e_err_options = ``e_v (v_err "IPv4OptionsNotSupported")``;
(* error.IPv4ChecksumError *)
val e_err_checksum = ``e_v (v_err "IPv4ChecksumError")``;
(* p.ethernet.etherType *)
val e_eth_ty = ``(e_acc (e_acc (e_var "p") (e_var "ethernet")) (e_var "etherType"))``;

(* start parser state *)
val stmt_start_extract = ``stmt_ass lval_null (e_ext_call (lval_varname "b") "extract" [(^e_eth)])``;
val stmt_start_trans = ``stmt_trans (e_select (^e_eth_ty) ([((^ether_ty_ok), "parse_ipv4")]) "reject")``;

val start_body = mk_stmt_seq_list [stmt_start_extract, stmt_start_trans];

(* parse_ipv4 parser state *)
val stmt_parse_ipv4_extract = ``stmt_ass lval_null (e_ext_call (lval_varname "b") "extract" [(^e_ip)])``;
val stmt_parse_ipv4_verify1 = ``stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)``;
val stmt_parse_ipv4_verify2 = ``stmt_verify (^e_ip_ihl_eq_4w5) (^e_err_options)``;
val stmt_parse_ipv4_clear = ``stmt_ass lval_null (e_ext_call (lval_varname "ck") "clear" [])``;
val stmt_parse_ipv4_update = ``stmt_ass lval_null (e_ext_call (lval_varname "ck") "update" [(^e_ip)])``;
val stmt_parse_ipv4_verify3 = ``stmt_verify (^e_ck_eq_16w0) (^e_err_checksum)``;
val stmt_parse_ipv4_trans = ``stmt_trans (e_var "accept")``;

val parse_ipv4_body =
  mk_stmt_seq_list [stmt_parse_ipv4_extract,
                    stmt_parse_ipv4_verify1,
                    stmt_parse_ipv4_verify2,
                    stmt_parse_ipv4_clear,
                    stmt_parse_ipv4_update,
                    stmt_parse_ipv4_verify3,
                    stmt_parse_ipv4_trans];

(*
(* TODO: Put string -> term functionality in list constructor *)
val test_header =
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
*)

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

val input_bl_eth_ok = ``fixwidth 112 (n2v 2048)``;
val input_bl_ipv4_ok = ``(fixwidth 4 (n2v 4))++(fixwidth 4 (n2v 5))++(extend F 72 [])++(fixwidth 16 (w2v ((-84w:word16))))++(extend F 64 [])``;
val input_bl_ok = ``(^input_bl_eth_ok)++(^input_bl_ipv4_ok)``;
val stacks_uninit_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_bl_ok)), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;
(* Stacks at parse_ipv4 state *)
val stacks_uninit_parse_ipv4_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_bl_ipv4_ok)), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;

val stacks_init_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_header T [("version", (^ip_v0_ok))]));
                                           ("ethernet", (v_header T [("etherType", (^ether_ty_ok))]))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;

val stacks_bad =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_header T [("version", (^ip_v0_bad))]))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;

(* ``:(string |-> (ext # (string # d) list))`` *)
val ext_map = ``FEMPTY |+ ("extract", (extract, [("hdr", d_out)]))
                       |+ ("clear", (clear, []))
                       |+ ("update", (update, [("data", d_in)]))
                       |+ ("get", (get, []))
                       |+ ("emit", (emit, [("data", d_in)]))
                       |+ ("isValid", (is_valid, [("hdr", d_in)]))``;
val ext_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, ``FEMPTY:func_map``, ``FEMPTY:pars_map``, ``FEMPTY:t_map``, ``ctrl:ctrl``];

val status = ``status_running``;

(* Test cases from the parser of the VSS example *)

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


(***************************)
(*   Match-action tests    *)

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

(* TODO: Move architectural constants to VSS architectural file? *)
val DROP_PORT_tm = mk_v_bitii (15, 4);
val CPU_OUT_PORT_tm = mk_v_bitii (15, 4);


val e_outport = mk_lval_field (mk_lval_varname "outCtrl", "outputPort");
val drop_action_fun = ``("Drop_action", (stmt_seq (stmt_ass (^e_outport) (e_v (^DROP_PORT_tm))) (stmt_ret (e_v v_bot))), []:(string # d) list)``;
val lval_headers_ip_ttl = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ip"), "ttl");
val e_headers_ip_ttl = mk_e_acc (mk_e_acc (mk_e_var "headers", mk_e_var "ip"), mk_e_var "ttl");
val set_nhop_fun = ``("Set_nhop", (^(mk_stmt_seq_list [(mk_stmt_ass (mk_lval_varname "nextHop", mk_e_var "ipv4_dest")),
                                                       (mk_stmt_ass (lval_headers_ip_ttl, mk_e_binop (e_headers_ip_ttl, binop_sub_tm, mk_e_v (mk_v_bitii (1, 8))))),
                                                       
                                                       (mk_stmt_ass (mk_lval_field (mk_lval_varname "outCtrl", "outputPort"), mk_e_var "port"))])), [("ipv4_dest", d_none); ("port", d_none)]:(string # d) list)``;
val send_to_cpu_fun = ``("Send_to_cpu", stmt_ass (^e_outport) (e_v (^CPU_OUT_PORT_tm)), []:(string # d) list)``;
val lval_ethdst = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "dstAddr");
val set_dmac_fun = ``("Set_dmac", stmt_ass (^lval_ethdst) (e_var "dmac"), [("dmac", d_none)]:(string # d) list)``;
val lval_ethsrc = mk_lval_field (mk_lval_field (mk_lval_varname "headers", "ethernet"), "srcAddr");
val set_smac_fun = ``("Set_smac", stmt_ass (^lval_ethsrc) (e_var "smac"), [("smac", d_none)]:(string # d) list)``;
val func_map = ``FEMPTY |+ (^drop_action_fun)
                        |+ (^set_nhop_fun)
                        |+ (^send_to_cpu_fun)
                        |+ (^set_dmac_fun)
                        |+ (^set_smac_fun)``;


val ipv4_match_table = ``("ipv4_match", (e_acc (e_acc (e_var "headers") (e_var "ip")) (e_var "dstAddr"), match_kind_lpm))``;
val check_ttl_table = ``("check_ttl", (e_acc (e_acc (e_var "headers") (e_var "ip")) (e_var "ttl"), match_kind_exact))``;
val dmac_table = ``("dmac", (e_var "nextHop", match_kind_exact))``;
val smac_table = ``("smac", (e_acc (e_var "outCtrl") (e_var "outputPort"), match_kind_exact))``;
val t_map = ``FEMPTY |+ (^ipv4_match_table)
                     |+ (^check_ttl_table)
                     |+ (^dmac_table)
                     |+ (^smac_table)``;


val toppipe_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, func_map, ``FEMPTY:pars_map``, t_map, ``ctrl:ctrl``];


val e_parseerror_cond = mk_e_binop (``(e_var "parseError")``, binop_neq_tm, ``(e_v (v_err "NoError"))``);
val stmt_parseerror_then = mk_stmt_seq (mk_stmt_ass (lval_null_tm, mk_e_func_call (``"Drop_action"``, ``[]:e list``)) , mk_stmt_ret ``e_v v_bot``);
val stmt_parseerror = mk_stmt_cond (e_parseerror_cond, stmt_parseerror_then, stmt_empty_tm);

val e_ipv4_match_cond = mk_e_binop (``(e_acc (e_var "outCtrl") (e_var "outputPort"))``, binop_eq_tm, mk_e_v DROP_PORT_tm);
val stmt_ipv4_match = mk_stmt_seq (mk_stmt_app (``"ipv4_match"``, ``e_v v_bot``), mk_stmt_cond (e_ipv4_match_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_check_ttl_cond = mk_e_binop (``(e_acc (e_var "outCtrl") (e_var "outputPort"))``, binop_eq_tm, mk_e_v CPU_OUT_PORT_tm);
val check_ttl_match = mk_stmt_seq (mk_stmt_app (``"check_ttl"``, ``e_v v_bot``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val e_dmac_cond = mk_e_binop (``(e_acc (e_var "outCtrl") (e_var "outputPort"))``, binop_eq_tm, mk_e_v DROP_PORT_tm);
val dmac_match = mk_stmt_seq (mk_stmt_app (``"dmac"``, ``e_v v_bot``), mk_stmt_cond (e_check_ttl_cond, mk_stmt_ret ``e_v v_bot``, stmt_empty_tm));

val smac_match = mk_stmt_app (``"smac"``, ``e_v v_bot``);

(* Test cases from the match-action pipeline of the VSS example *)
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
  (``stmt_multi_exec (^toppipe_ctx) (^stmt_ipv4_match) (^stacks_postparser_ok) status_running 1``, NONE:term option),
  (*
  check_ttl.apply();
  if (outCtrl.outputPort == CPU_OUT_PORT) return;
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^check_ttl_match) (^stacks_postparser_ok) status_running 1``, NONE:term option),
  (*
  dmac.apply();
  if (outCtrl.outputPort == DROP_PORT) return;
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^dmac_match) (^stacks_postparser_ok) status_running 1``, NONE:term option),
  (*
  smac.apply();
  *)
  (``stmt_multi_exec (^toppipe_ctx) (^smac_match) (^stacks_postparser_ok) status_running 1``, NONE:term option)
];

(* Test match-action pipeline VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_matchaction_test_cases;

(***********************)
(*   Deparser tests    *)

val deparser_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, ``FEMPTY:func_map``, ``FEMPTY:pars_map``, t_map, ``ctrl:ctrl``];

(* NOTE: This does not include any effects from the match-action part *)
val stacks_postmatchaction_ok =
 ``stacks_tup ([FEMPTY |+ ("p", ((^parsed_packet_struct_postparser), NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_out []), NONE)) |+
                          ("ck", (v_ext (ext_obj_ck 0w), NONE))]:scope list) ([]:call_stack)``;


val stmt_deparser_emit = ``stmt_ass lval_null (e_ext_call "b" "emit" [(^e_eth)])``;

val stmt_deparser_cond = ``stmt_cond (e_ext_call "p" "isValid" []) () ()``;

val vss_deparser_test_cases = [
  (*
  b.emit(p.ethernet);
  if (p.ip.isValid()) {
      ck.clear();              // prepare checksum unit
      p.ip.hdrChecksum = 16w0; // clear checksum
      ck.update(p.ip);         // compute new checksum.
      p.ip.hdrChecksum = ck.get();
  }
  b.emit(p.ip);
  *)
];

(* Test match-action pipeline VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_deparser_test_cases;
