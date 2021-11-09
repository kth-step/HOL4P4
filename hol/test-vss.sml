open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open p4Syntax;
open pairSyntax;
open testLib;
open p4_exec_semTheory;
open p4_coreTheory;
open blastLib;

(*************************************************************************************)
(* This file includes some tests run on fragments of the VSS example in the P4 spec. *)
(*************************************************************************************)

(*************************)
(*   From VSS Example    *)
(*************************)

val ip_v0_ok = mk_v_bitii (4, 4);
val ip_v0_bad = mk_v_bitii (3, 4);
val ether_ty_ok = mk_v_bitii (2048, 16);
(* TODO: Use syntax functions *)

val e_ip_v = ``(e_acc (e_acc (e_var "p") (e_var "ip")) (e_var "version"))``;
val e_4w4 = mk_e_v ip_v0_ok;
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``;

val e_err_version = ``e_v (v_err "IPv4IncorrectVersion")``;

val e_eth_ty = ``(e_acc (e_acc (e_var "p") (e_var "ethernet")) (e_var "etherType"))``;

(*
val test_struct =  mk_v_struct_list [(``"version"``, ``^ip_v0_ok``)]
*)

val stacks_ok =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_struct [("version", (^ip_v0_ok))]));
                                           ("ethernet", (v_struct [("etherType", (^ether_ty_ok))]))], NONE)) |+
                ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;
val stacks_bad =
 ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_struct [("version", (^ip_v0_bad))]))], NONE)) |+
                ("parseError", (v_err "NoError", NONE))]:scope list) ([]:call_stack)``;
val status = ``status_running``;

(* WIP test cases:

b.extract(p.ethernet);

b.extract(p.ip);

*)

val vss_test_cases = [
  (*
  p.ip.version == 4w4
  *)
  (``e_multi_exec ctx (^e_ip_v_eq_4w4) (^stacks_ok) (^status) 20``, NONE),
  (*
  verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
  *)
  (``stmt_multi_exec ctx (stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)) (^stacks_ok) (^status) 20``,
   SOME ``stmt_empty``),
  (``stmt_multi_exec ctx (stmt_verify (^e_ip_v_eq_4w4) (^e_err_version)) (^stacks_bad) (^status) 20``,
   SOME ``stmt_empty``),
  (*
  transition select(p.ethernet.etherType) {
      0x0800: parse_ipv4;
      // no default rule: all other packets rejected
  }
  *)
  (``stmt_multi_exec ctx (stmt_trans (e_select (^e_eth_ty) ([((^ether_ty_ok), "parse_ipv4")]) "reject")) (^stacks_ok) (^status) 20``,
   SOME ``stmt_empty``)
];

fun eval_stmt_multi_exec tm =
 let
  val res_thm = EVAL tm
  (* TODO: Fix p4_v2w_ss for arbitrary width *)
  val res_canon_thm = SIMP_RULE (pure_ss++p4_v2w_ss) [] res_thm
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
