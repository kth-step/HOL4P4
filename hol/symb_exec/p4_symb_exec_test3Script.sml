open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execLib;

val _ = new_theory "p4_symb_exec_test3";

(* Test 3:
 * There's a single select expression that branches on the LSB.
 * Postcondition holds only for "accept".
 * The precondition states that the accept case should be selected.
 *
 * This tests if branching on select statement and following pruning works. *)

val symb_exec3_blftymap = ``[]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val symb_exec3_ftymap = ``[]:((funn, (p_tau list # p_tau)) alist)``;

val symb_exec3_pblock_action_names_map = ``[]:((string, (string, string list) alist) alist)``;

val symb_exec3_actx = ``([arch_block_inp;
  arch_block_pbl "p"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "vrfy" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "ingress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "egress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "update" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "deparser" [e_var (varn_name "b"); e_var (varn_name "hdr")];
  arch_block_out],
 [("p",pbl_type_parser,
   [("b",d_none); ("h",d_out); ("m",d_inout); ("sm",d_inout)],
   [("p",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [(varn_name "sel_e",tau_bit 1,NONE)],
   [("start",
     stmt_seq
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_in" "extract")
                [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"]))
          (stmt_ass (lval_varname (varn_name "sel_e"))
             (e_cast (cast_unsigned 1)
                (e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e"))))
       (stmt_trans
          (e_select (e_struct [("",e_var (varn_name "sel_e"))])
             [([s_sing (v_bit ([T],1))],"accept");
              ([s_sing (v_bit ([F],1))],"reject")] "set_no_match")));
    ("set_no_match",
     stmt_ass lval_null
       (e_call (funn_ext "" "verify")
          [e_v (v_bool F);
           e_v
             (v_bit
                ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                  F; F; F; F; F; F; F; F; F; F; T; F],32))]))],[]);
  ("vrfy",pbl_type_control,[("h",d_inout); ("m",d_inout)],
   [("vrfy",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("update",pbl_type_control,[("h",d_inout); ("m",d_inout)],
   [("update",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("egress",pbl_type_control,[("h",d_inout); ("m",d_inout); ("sm",d_inout)],
   [("egress",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("deparser",pbl_type_control,[("b",d_none); ("h",d_in)],
   [("deparser",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "packet_out" "emit")
             [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"])),[])],
   [],[],[]);
  ("ingress",pbl_type_control,
   [("h",d_inout); ("m",d_inout); ("standard_meta",d_inout)],
   [("ingress",
     stmt_seq stmt_empty
       (stmt_ass
          (lval_field (lval_varname (varn_name "standard_meta"))
             "egress_spec") (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9)))),[])],
   [],[],[])],[("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f
   (v_struct
      [("h",
        v_header ARB
          [("row",
            v_struct
              [("e",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("t",
                v_bit
                  ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                    ARB; ARB; ARB; ARB; ARB],16));
               ("l",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("r",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("v",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8))])])],
    v_struct []),v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify);
    ("verify_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_in); ("algo",d_none)],
     v1model_verify_checksum);
    ("update_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_inout);
      ("algo",d_none)],v1model_update_checksum)]);
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
 [("NoAction",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; F],32)))]))
        stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in)])]):v1model_ascope actx``;

val symb_exec3_astate_symb = rhs $ concl $ EVAL “p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] ((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],[]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool ARB); ("miss",v_bool ARB);
       ("action_run",v_bit (REPLICATE 32 ARB,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate”;


(* symb_exec: *)
(* Parameter assignment for debugging: *)
val debug_flag = false
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec3_actx
val (fty_map, b_fty_map, pblock_action_names_map) = (symb_exec3_ftymap, symb_exec3_blftymap, symb_exec3_pblock_action_names_map)
val const_actions_tables = []
val path_cond_defs = []
val init_astate = symb_exec3_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val path_cond = ASSUME “e8 = T”
val p4_is_finished_alt_opt = NONE
val n_max = 50;
val postcond = “(\s. packet_has_port s 1):v1model_ascope astate -> bool”;
(* For debugging:
val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] p4_exec_semTheory.arch_multi_exec_comp_n_tl_assl
*)

(* For debugging, branch happens here:
val [(path_cond_res, step_thm), (path_cond2_res, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 25;
*)

(*
  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))
*)

(* Finishes at 45 steps (one step of which is a symbolic branch)
 * (higher numbers as arguments will work, but do no extra computations) *)
val contract_thm = p4_symb_exec_prove_contract_conc debug_flag arch_ty ctx (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt n_max postcond;

val _ = export_theory ();
