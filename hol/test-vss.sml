open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open p4Syntax;
open pairSyntax;
open testLib;
open p4Lib;
open p4_exec_semTheory;
open p4_coreTheory;
open blastLib;

(*************************************************************************************)
(* This file includes some tests run on fragments of the VSS example in the P4 spec. *)
(*************************************************************************************)

(*************************)
(*   From VSS Example    *)
(*************************)

(* 0x0800 *)
val ether_ty_ok = mk_v_bitii (2048, 16);

(* 4w4 *)
val ip_v0_ok = mk_v_bitii (4, 4);
(* 4w3 *)
val ip_v0_bad = mk_v_bitii (3, 4);
(* 4w5 *)
val ip_ihl_ok = mk_v_bitii (5, 4);

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
(* p.ip.version == 4w4 *)
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``;
(* p.ip.ihl == 4w5 *)
val e_ip_ihl_eq_4w5 = ``e_binop (^e_ip_ihl) binop_eq (^e_4w5)``;

(* error.IPv4IncorrectVersion *)
val e_err_version = ``e_v (v_err "IPv4IncorrectVersion")``;
(* error.IPv4OptionsNotSupported *)
val e_err_options = ``e_v (v_err "IPv4OptionsNotSupported")``;
(* p.ethernet.etherType *)
val e_eth_ty = ``(e_acc (e_acc (e_var "p") (e_var "ethernet")) (e_var "etherType"))``;

(* start parser state *)
val stmt_start_extract = ``stmt_ass lval_null (e_ext_call "b" "extract" [(^e_eth)])``;
val stmt_start_trans = ``stmt_trans (e_select (^e_eth_ty) ([((^ether_ty_ok), "parse_ipv4")]) "reject")``;

val start_body = mk_stmt_seq_list [stmt_start_extract, stmt_start_trans];

(* parse_ipv4 parser state *)
val stmt_parse_ipv4_extract = ``stmt_ass lval_null (e_ext_call "b" "extract" [(^e_ip)])``;
val stmt_parse_ipv4_verify1 = ``stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)``;
val stmt_parse_ipv4_verify2 = ``stmt_verify (^e_ip_ihl_eq_4w5) (^e_err_options)``;
val stmt_parse_ipv4_trans = ``stmt_trans (e_var "accept")``;

val parse_ipv4_body =
  mk_stmt_seq_list [stmt_parse_ipv4_extract,
                    stmt_parse_ipv4_verify1,
                    stmt_parse_ipv4_verify2,
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
val input_bl_ipv4_ok = ``(fixwidth 4 (n2v 4))++(fixwidth 4 (n2v 5))++(extend F 152 [])``;
val input_bl_ok = ``(^input_bl_eth_ok)++(^input_bl_ipv4_ok)``;
val stacks_uninit_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_bl_ok)), NONE))]:scope list) ([]:call_stack)``;
(* Stacks at parse_ipv4 state *)
val stacks_uninit_parse_ipv4_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (^parsed_packet_struct_uninit, NONE)) |+
                          ("parseError", (v_err "NoError", NONE)) |+
                          ("b", (v_ext (ext_obj_in (^input_bl_ipv4_ok)), NONE))]:scope list) ([]:call_stack)``;

val stacks_init_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_header T [("version", (^ip_v0_ok))]));
                                           ("ethernet", (v_header T [("etherType", (^ether_ty_ok))]))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;

val stacks_bad =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_header T [("version", (^ip_v0_bad))]))], NONE)) |+
                          ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;

(* ``:(string |-> (ext # (string # d) list))`` *)
val ext_map = ``FEMPTY |+ ("extract", (extract, [("hdr", d_out)]))``;
val ext_ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, ext_map, ``FEMPTY:func_map``, ``FEMPTY:pars_map``, ``FEMPTY:t_map``, ``ctrl:ctrl``];

val status = ``status_running``;

(* WIP test cases:

(* ck.clear(); *)

(* ck.update(p.ip); *)


(* ck.get() *)



*)

val vss_test_cases = [
  (*
  b.extract(p.ethernet);
  *)
  (``stmt_multi_exec (^ext_ctx) (^stmt_start_extract) (^stacks_uninit_ok) (^status) 20``, NONE),
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
  b.extract(p.ip);
  verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
  verify(p.ip.ihl == 4w5, error.IPv4OptionsNotSupported);
  transition accept;
  *)
  (``stmt_multi_exec (^ext_ctx) (^parse_ipv4_body) (^stacks_uninit_parse_ipv4_ok) (^status) 20``,
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

(* Test VSS fragments *)
val _ = test_red ("eval_stmt_multi_exec", eval_stmt_multi_exec)
                 ("is_multi_exec_res_well_formed", is_multi_exec_res_well_formed)
                 vss_test_cases;
