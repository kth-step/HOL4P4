open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execLib;

val _ = new_theory "table_unknown";

(* Test 6:
 * There are two table applications, one with two possible outcomes,
 * one with unknown outcome (totally unknown table configuration).
 *
 * This tests if regular branching on apply statement and
 * branching on apply statements with unknown table entries works. *)

val symb_exec6_blftymap =
 ``[("ingress", [(funn_name "set_default_out_port", ([], p_tau_bot));
                 (funn_name "set_out_port", ([p_tau_bit 9], p_tau_bot));
                 (funn_name "set_l", ([p_tau_bit 8], p_tau_bot))])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val symb_exec6_ftymap = ``[(funn_name "NoAction", ([], p_tau_bot))]:((funn, (p_tau list # p_tau)) alist)``;

val symb_exec6_pblock_action_names_map = ``[("ingress", [("t2", ["NoAction"; "set_l"])])]:((string, (string, string list) alist) alist)``;

val symb_exec6_actx = ``([arch_block_inp;
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
   [("p",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],[],
   [("start",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
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
       (stmt_seq
          (stmt_app "t1"
             [e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e"])
          (stmt_app "t2"
             [e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e"])),
     []);
    ("set_l",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field (lval_field (lval_varname (varn_name "h")) "h")
                   "row") "l") (e_var (varn_name "x")))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("x",d_none)]);
    ("set_out_port",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_var (varn_name "x")))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("x",d_none)]);
    ("set_default_out_port",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_v (v_bit ([F; F; T; T; F; F; T; F; T],9))))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)])],[],
   [],
   [("t2",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("t1",[mk_exact],
     "set_default_out_port",[e_v (v_bool T); e_v (v_bool F)])])],
 [("postparser",ffblock_ff v1model_postparser)],
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
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)]);
  ("ipsec_crypt",SOME ([("this",d_out)],ipsec_crypt_construct),
   [("decrypt_aes_ctr",
     [("ipv4",d_inout); ("esp",d_inout); ("standard_metadata",d_inout);
      ("key",d_in); ("key_hmac",d_in)],ipsec_crypt_decrypt_aes_ctr);
    ("encrypt_aes_ctr",
     [("ipv4",d_inout); ("esp",d_inout); ("key",d_in); ("key_hmac",d_in)],
     ipsec_crypt_encrypt_aes_ctr);
    ("encrypt_null",[("ipv4",d_inout); ("esp",d_inout)],
     ipsec_crypt_encrypt_null);
    ("decrypt_null",
     [("ipv4",d_inout); ("esp",d_inout); ("standard_metadata",d_inout)],
     ipsec_crypt_decrypt_null)])],
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

val symb_exec6_astate_symb = rhs $ concl $ EVAL ``p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] ((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
  [("t2",t2_ctrl);
   ("t1",
    [(((λk.
            match_all
              (ZIP
                 (MAP (λe. THE (v_of_e e)) k,
                  [s_sing (v_bit ([F; F; F; F; F; F; F; T],8))]))),0),
      "set_out_port",
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; T; F; T; F; T; F],9))]);
     (((λk.
            match_all
              (ZIP
                 (MAP (λe. THE (v_of_e e)) k,
                  [s_sing (v_bit ([F; F; F; F; F; F; T; F],8))]))),0),
      "set_out_port",
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; T; F; T; T; T; T],9))]);
     (((λk.
            match_all
              (ZIP
                 (MAP (λe. THE (v_of_e e)) k,
                  [s_sing (v_bit ([F; F; F; F; F; F; T; T],8))]))),0),
      "set_out_port",
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; F; F; T; T; F; T],9))])])]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool ARB); ("miss",v_bool ARB);
       ("action_run",v_bit (REPLICATE 32 ARB,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate``;

(* Additional parts of the context relevant only to symbolic execution *)
val fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_ftymap_entries ^symb_exec6_ftymap”
val b_fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_b_ftymap_entries ^symb_exec6_blftymap”

val symb_exec6_ctx_tm = “(^fty_map', ^b_fty_map', ^symb_exec6_pblock_action_names_map)”
val symb_exec_ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "symb_exec_ctx" (mk_eq(mk_var("symb_exec_ctx", type_of symb_exec6_ctx_tm), symb_exec6_ctx_tm))

val symb_exec6_pblock_map = #2 $ p4Syntax.dest_actx symb_exec6_actx;
val symb_exec_pblock_map_def = hd $ Defn.eqns_of $ Defn.mk_defn "pblock_map" (mk_eq(mk_var("pblock_map", type_of symb_exec6_pblock_map), symb_exec6_pblock_map))
val symb_exec6_ctrl = #4 $ p4_v1modelLib.dest_v1model_ascope $ #4 $ p4Syntax.dest_aenv $ #1 $ p4Syntax.dest_astate symb_exec6_astate_symb;
val symb_exec6_wf_tm = “v1model_ctrl_is_well_formed ^(lhs $ concl symb_exec_ctx_def) ^(lhs $ concl symb_exec_pblock_map_def) (^symb_exec6_ctrl)”
val symb_exec6_wf_tbl_tm = “v1model_tbl_is_well_formed ^(lhs $ concl symb_exec_ctx_def) ^(lhs $ concl symb_exec_pblock_map_def) ("t2",t2_ctrl)”


(* Parameter assignment for debugging: *)
val debug_flag = false;
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec6_actx
val (fty_map, b_fty_map, pblock_action_names_map) = (symb_exec6_ftymap, symb_exec6_blftymap, symb_exec6_pblock_action_names_map)
val const_actions_tables = ["t1"]
val path_cond_defs = [symb_exec_ctx_def, symb_exec_pblock_map_def]
val init_astate = symb_exec6_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val thms_to_add = []
val path_cond = ASSUME “e8 = T /\ ^symb_exec6_wf_tbl_tm”
val p4_is_finished_alt_opt = NONE
val n_max = 150;
val postcond = “(\s. T):v1model_ascope astate -> bool”;
val fuel = 1;
val postcond_rewr_thms = []
val postcond_simpset = pure_ss

(* For debugging:
val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] p4_exec_semTheory.arch_multi_exec_comp_n_tl_assl
val init_step_thm = eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 0))

val ctx_name = "ctx"
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

(*
val norewr_eval_ctxt = p4_get_norewr_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts), thms_to_add, (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
val eval_ctxt = p4_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts), (stop_consts_never@p4_stop_eval_consts), (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
*)

val lang_regular_step = p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm;
val lang_init_step_thm = init_step_thm;
val lang_should_branch = p4_should_branch (fty_map', b_fty_map') const_actions_tables' ctx_def;
val lang_is_finished = is_finished;

(* Remaining fuel *)
val fuel = 1;
val nobranch_flag = false;
val npaths = 1;
*)

(* For debugging, first apply happens here, after step 23:

val (path_tree, [(path_id, path_cond_res, step_thm)]) =
 p4_symb_exec 1 false arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond NONE 23;

* Second apply happens here, after step 44:

val (path_tree, [(n, path_cond_res, step_thm), (n2, path_cond2_res, step_thm2), (n3, path_cond3_res, step_thm3), (n4, path_cond4_res, step_thm4)]) =
 p4_symb_exec false arch_ty (ctx_def, ctx) (fty_map, b_fty_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond NONE 44;

val path_cond = path_cond2_res;
val step_thm = step_thm2;

*)


val time_start = Time.now();
(*
val p4_symb_exec_fun = (p4_symb_exec 1)
*)
val contract_thm = p4_symb_exec_prove_contract debug_flag arch_ty (def_term ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt n_max postcond postcond_rewr_thms postcond_simpset;

val _ = print (String.concat ["Total time consumption: ",
                              (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
                              " ms\n"]);

val _ = export_theory ();
