open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execTheory p4_symb_execLib;

val _ = new_theory "decompose";

(* There's a single if-statement that branches on symbolic bits.
 * Postcondition holds regardless of which path was taken.
 *
 * This tests if basic branching and unification works.
 * In addition, the verification is split up into verificaiton of the first
 * programmable block, and the subsequent. *)

val symb_exec1_blftymap = ``[]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val symb_exec1_ftymap = ``[]:((funn, (p_tau list # p_tau)) alist)``;

val symb_exec1_pblock_action_names_map = ``[]:((string, (string, string list) alist) alist)``;

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
val (fty_map, b_fty_map, pblock_action_names_map) = (symb_exec1_ftymap, symb_exec1_blftymap, symb_exec1_pblock_action_names_map)
val const_actions_tables = []
val path_cond_defs = []
val init_astate = symb_exec1_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val thms_to_add = []
val path_cond = (ASSUME T)
val p4_is_finished_alt_opt = NONE
val n_max = 50;
val postcond = “(\s. packet_has_port s 1 \/ packet_has_port s 2):v1model_ascope astate -> bool”;
val postcond_rewr_thms = [p4_symb_execTheory.packet_has_port_def]


(* State finish criterion: "block about to start has index block_index_stop" *)
(* Straightforward from index 2 to 4, problem at 5 since disjunction is needed *)
val block_index_stop = “2:num”
val p4_is_finished_alt_opt1 = SOME (fn step_thm => Teq $ rhs $ concl $ EVAL “p4_block_next ^(optionSyntax.dest_some $ rhs $ snd $ dest_imp $ concl step_thm) ^block_index_stop”);


(* TODO: Why does the initial state not have anything mapped to by ext reference 1? *)
(* Get well-formedness property after parser block just finished *)
val p4_v1model_parser_wellformed_def = (fn defn => let val _ = Defn.save_defn defn in Defn.fetch_eqns defn end) $ get_v1model_wellformed_defs ctx init_astate block_index_stop;
val postcond_simpset = (pure_ss++(p4_wellformed_ss p4_v1model_parser_wellformed_def))


(* Define ctx outside p4_symb_execLib, to avoid re-definitions *)
val ctx_name = "ctx"
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

(* Get intermediate state *)
val (path_tree1, res_list1) =
 p4_symb_exec 1 debug_flag arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt1 50;
val (fv_index1, disj_thm1, step_thm1) = hd res_list1

(* 1. Prove a contract from initial to intermediate state *)
(* Last conjunct needed for block_index stop from 3 onwards *)
val postcond1 = “(\s. p4_v1model_parser_wellformed s /\
                      p4_v1model_lookup_avar (lval_field (lval_field (lval_field (lval_varname (varn_name "parsedHdr")) "h") "row") "e") s = SOME $ v_bit ([e1; e2; e3; e4; e5; e6; e7; e8],8) /\
                      p4_v1model_lookup_avar_validity (lval_field (lval_varname (varn_name "parsedHdr")) "h") s = SOME T (* /\
                      p4_v1model_lookup_avar_validity (lval_field (lval_varname (varn_name "hdr")) "h") s = SOME T *) ):v1model_ascope astate -> bool”;
(*
(* If block_index_stop is 5 or later *)
(* TODO: Problems when using disjunctions: "egress_spec is either 1 or 2" *)
val postcond1 = “(\s. p4_v1model_parser_wellformed s /\
                      p4_v1model_lookup_avar (lval_field (lval_field (lval_field (lval_varname (varn_name "parsedHdr")) "h") "row") "e") s = SOME $ v_bit ([e1; e2; e3; e4; e5; e6; e7; e8],8) /\
                      (p4_v1model_lookup_avar (lval_field (lval_varname (varn_name "standard_meta")) "egress_spec") s = SOME $ v_bit ([F; F; F; F; F; F; F; F; T],9) \/
                       p4_v1model_lookup_avar (lval_field (lval_varname (varn_name "standard_meta")) "egress_spec") s = SOME $ v_bit ([F; F; F; F; F; F; F; T; F],9)) /\
                      p4_v1model_lookup_avar_validity (lval_field (lval_varname (varn_name "parsedHdr")) "h") s = SOME T /\
                      p4_v1model_lookup_avar_validity (lval_field (lval_varname (varn_name "hdr")) "h") s = SOME T):v1model_ascope astate -> bool”;
*)
val postcond_rewr_thms1 = [p4_v1model_parser_wellformed_def, p4_v1model_lookup_avar_def, p4_v1model_lookup_avar_validity_def, lookup_lval_def, p4_v1modelTheory.v_map_to_scope_def]
(* DEBUG

val p4_is_finished_alt_opt = p4_is_finished_alt_opt1
val postcond = postcond1
val postcond_rewr_thms = postcond_rewr_thms1

*)
val contract_thm1 = p4_symb_exec_prove_contract debug_flag arch_ty (def_thm ctx_def) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt1 n_max postcond1 postcond_rewr_thms1 postcond_simpset;

(* 2. Introduce a new initial state from the fact that p4_v1model_parser_wellformed holds.
 *    The weakest possible state that satisfies WF: this is the state where all
 *    the existentially quantified variables are free variables. This can be obtained from the
 *    definition *)
val init_astate2 = get_intermediate_state postcond1 p4_v1model_parser_wellformed_def;

(* 3. Prove a contract from the intermediate to final state *)
(* TODO: Contact unification fails when disjunctions in the path condition are involved.
 *       Use simpset for p4_v1model_lookup_avar and similar?
 * Also, the initial path condition should maybe be the initial path condition combined with
 * the postcondition? *)
val contract_thm2 = p4_symb_exec_prove_contract debug_flag arch_ty (def_thm ctx_def) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate2 stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt n_max postcond postcond_rewr_thms postcond_simpset;

(* 4. Combine the contracts *)
(*
val contract1 = contract_thm1
val contract2 = contract_thm2
val wellformed_def = p4_v1model_parser_wellformed_def
*)
val combined_contract = p4_combine_contracts contract_thm1 contract_thm2 p4_v1model_parser_wellformed_def;

val _ = export_theory ();
