open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execLib;

val _ = new_theory "p4_symb_exec_test1";

(* Test 1:
 * There's a single if-statement that branches on symbolic bits.
 * Postcondition holds regardless of which path was taken.
 *
 * This tests if basic branching and unification works. *)

val symb_exec1_blftymap = ``[]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val symb_exec1_ftymap = ``[]:((funn, (p_tau list # p_tau)) alist)``;

val symb_exec1_actx = ``([arch_block_inp;
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
       (stmt_cond
          (e_binop
             (e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e")
             binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))))),
     [])],[],[],[])],[("postparser",ffblock_ff v1model_postparser)],
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


(*
(* Concrete state from old example program *)
val symb_exec1_astate = rhs $ concl $ EVAL “(p4_append_input_list [([F; F; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; T; F; F; F; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; F; T; T; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; T; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;
*)

(*
(* eval_under_assum: *)
GEN_ALL $ eval_under_assum p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate [] [] (ASSUME T) 10;
*)

(* As symbolic packet, generate something like this:
  
   data = [b1; b2; b3; b4; b5; b6; b7; b8]
   port = p

*)

val symb_exec1_astate_symb = rhs $ concl $ EVAL “p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] ((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],[]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool ARB); ("miss",v_bool ARB);
       ("action_run",v_bit (REPLICATE 32 ARB,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate”;

(* symb_exec: *)
(* Parameter assignment for debugging: *)
val debug_flag = false;
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec1_actx
val (fty_map, b_fty_map) = (symb_exec1_ftymap, symb_exec1_blftymap)
val const_actions_tables = []
val init_astate = symb_exec1_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val path_cond = (ASSUME T)
val p4_is_finished_alt_opt = NONE
val n_max = 50;
val postcond = “(\s. packet_has_port s 1 \/ packet_has_port s 2):v1model_ascope astate -> bool”;
(* For debugging:
val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] p4_exec_semTheory.arch_multi_exec_comp_n_tl_assl

val fuel = 1
*)

(* For debugging, branch happens here:

val (path_tree, [(path_id, path_cond, step_thm)]) =
 p4_symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 24;

val (path_tree, [(path_id, path_cond, step_thm), (path_id2, path_cond2, step_thm2)]) =
 p4_symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 25;

   Join happens here:
val (path_tree, [(path_id, path_cond_res, step_thm)]) =
 p4_symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 44;

val [res_elem1, res_elem2] = res_elems

val (res_id1, res_cond1, res_thm1) = res_elem1
*)

(* Finishes at 45 steps (one step of which is a symbolic branch)
 * (higher numbers as arguments will work, but do no extra computations) *)
val contract_thm = p4_symb_exec_prove_contract_conc debug_flag arch_ty ctx (symb_exec1_ftymap, symb_exec1_blftymap) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond p4_is_finished_alt_opt n_max postcond;

(*

val path_cond = (ASSUME T);
val n_max = 50;
val postcond = “(\s. packet_has_port s 1 \/ packet_has_port s 2):v1model_ascope astate -> bool”;
val nthreads_max = 1;
val debug_flag = false;
val fuel = 100

  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

  val table_stop_consts = [match_all_tm]
  val eval_ctxt = p4_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts), (stop_consts_never@p4_stop_eval_consts), (fn astate => mk_arch_multi_exec (ctx, astate, 1)))

val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] p4_exec_semTheory.arch_multi_exec_comp_n_tl_assl

  val p4_init_step_thm = eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 0))

symb_exec_conc (p4_regular_step (debug_flag, ctx_def, ctx, eval_ctxt) comp_thm, p4_init_step_thm, p4_should_branch, p4_is_finished) path_cond fuel 4

*)

val _ = export_theory ();
