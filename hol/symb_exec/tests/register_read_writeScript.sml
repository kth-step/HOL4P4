open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execLib;

val _ = new_theory "register_read_write";

(* Test 8:
 * There is a large register array. This is read from, then written to, at an index
 * using symbolic bits.
 * The test checks that the symbolic execution does not crash when reading from and
 * writing to registers.*)

val symb_exec8_blftymap = ``[("p",[]); ("vrfy",[]); ("update",[]); ("egress",[]); ("deparser",[]);
 ("ingress",[])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val symb_exec8_ftymap = ``[(funn_ext "Checksum16" "get",[p_tau_par "D9"],p_tau_bit 16);
 (funn_inst "Checksum16",[],p_tau_ext "Checksum16");
 (funn_inst "action_selector",
  [p_tau_par "HashAlgorithm"; p_tau_bit 32; p_tau_bit 32],
  p_tau_ext "action_selector");
 (funn_inst "action_profile",[p_tau_bit 32],p_tau_ext "action_profile");
 (funn_ext "register" "write",[p_tau_bit 32; p_tau_par "T5"],p_tau_bot);
 (funn_ext "register" "read",[p_tau_par "T5"; p_tau_bit 32],p_tau_bot);
 (funn_inst "register",[p_tau_bit 32],p_tau_ext "register");
 (funn_ext "direct_meter" "read",[p_tau_par "T4"],p_tau_bot);
 (funn_inst "direct_meter",[p_tau_par "MeterType"],p_tau_ext "direct_meter");
 (funn_ext "meter" "execute_meter",[p_tau_bit 32; p_tau_par "T3"],p_tau_bot);
 (funn_inst "meter",[p_tau_bit 32; p_tau_par "MeterType"],p_tau_ext "meter");
 (funn_ext "direct_counter" "count",[],p_tau_bot);
 (funn_inst "direct_counter",[p_tau_par "CounterType"],
  p_tau_ext "direct_counter");
 (funn_ext "counter" "count",[p_tau_bit 32],p_tau_bot);
 (funn_inst "counter",[p_tau_bit 32; p_tau_par "CounterType"],
  p_tau_ext "counter");
 (funn_ext "packet_out" "emit",[p_tau_par "T2"],p_tau_bot);
 (funn_ext "packet_in" "length",[],p_tau_bit 32);
 (funn_ext "packet_in" "advance",[p_tau_bit 32],p_tau_bot);
 (funn_ext "packet_in" "lookahead",[],p_tau_par "T1");
 (funn_ext "packet_in" "extract",[p_tau_par "T0"; p_tau_bit 32],p_tau_bot);
 (funn_ext "packet_in" "extract",[p_tau_par "T"],p_tau_bot);
 (funn_ext "header" "isValid",[],p_tau_bool);
 (funn_ext "header" "setValid",[],p_tau_bot);
 (funn_ext "header" "setInvalid",[],p_tau_bot);
 (funn_ext "" "verify",[p_tau_bool; p_tau_bit 32],p_tau_bot);
 (funn_name "NoAction",[],p_tau_bot);
 (funn_ext "" "random",[p_tau_par "T6"; p_tau_par "T6"; p_tau_par "T6"],
  p_tau_bot);
 (funn_ext "" "digest",[p_tau_bit 32; p_tau_par "T7"],p_tau_bot);
 (funn_ext "" "mark_to_drop",
  [p_tau_xtl struct_ty_struct
     [("ingress_port",p_tau_bit 9); ("egress_spec",p_tau_bit 9);
      ("egress_port",p_tau_bit 9); ("instance_type",p_tau_bit 32);
      ("packet_length",p_tau_bit 32); ("enq_timestamp",p_tau_bit 32);
      ("enq_qdepth",p_tau_bit 19); ("deq_timedelta",p_tau_bit 32);
      ("deq_qdepth",p_tau_bit 19); ("ingress_global_timestamp",p_tau_bit 48);
      ("egress_global_timestamp",p_tau_bit 48); ("mcast_grp",p_tau_bit 16);
      ("egress_rid",p_tau_bit 16); ("checksum_error",p_tau_bit 1);
      ("parser_error",p_tau_bit 32); ("priority",p_tau_bit 3)]],p_tau_bot);
 (funn_ext "" "hash",
  [p_tau_par "O"; p_tau_par "HashAlgorithm"; p_tau_par "T8"; p_tau_par "D";
   p_tau_par "M"],p_tau_bot);
 (funn_ext "" "verify_checksum",
  [p_tau_bool; p_tau_par "T10"; p_tau_par "O11"; p_tau_par "HashAlgorithm"],
  p_tau_bot);
 (funn_ext "" "update_checksum",
  [p_tau_bool; p_tau_par "T12"; p_tau_par "O13"; p_tau_par "HashAlgorithm"],
  p_tau_bot);
 (funn_ext "" "verify_checksum_with_payload",
  [p_tau_bool; p_tau_par "T14"; p_tau_par "O15"; p_tau_par "HashAlgorithm"],
  p_tau_bot);
 (funn_ext "" "update_checksum_with_payload",
  [p_tau_bool; p_tau_par "T16"; p_tau_par "O17"; p_tau_par "HashAlgorithm"],
  p_tau_bot);
 (funn_ext "" "clone",[p_tau_par "CloneType"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "resubmit",[p_tau_par "T18"],p_tau_bot);
 (funn_ext "" "resubmit_preserving_field_list",[p_tau_bit 8],p_tau_bot);
 (funn_ext "" "recirculate",[p_tau_par "T19"],p_tau_bot);
 (funn_ext "" "recirculate_preserving_field_list",[p_tau_bit 8],p_tau_bot);
 (funn_ext "" "clone3",
  [p_tau_par "CloneType"; p_tau_bit 32; p_tau_par "T20"],p_tau_bot);
 (funn_ext "" "clone_preserving_field_list",
  [p_tau_par "CloneType"; p_tau_bit 32; p_tau_bit 8],p_tau_bot);
 (funn_ext "" "truncate",[p_tau_bit 32],p_tau_bot);
 (funn_ext "" "assert",[p_tau_bool],p_tau_bot);
 (funn_ext "" "assume",[p_tau_bool],p_tau_bot);
 (funn_ext "" "log_msg",[p_tau_bot; p_tau_par "T21"],p_tau_bot)]:((funn, (p_tau list # p_tau)) alist)``;

val symb_exec8_pblock_action_names_map = ``[("p",[]); ("vrfy",[]); ("update",[]); ("egress",[]); ("deparser",[]);
 ("ingress",[])]:((string, ((string, string) alist)) alist)``;

val symb_exec8_actx = ``([arch_block_inp;
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
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_inst "register")
             [e_var (varn_name "counters");
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; T; F; F; F; F; F; F; F; F; F; F],32));
              e_v
                (v_bit
                   ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                     ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                     ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32))]))
       (stmt_block [(varn_name "tmp",tau_bit 32,NONE)]
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "register" "read")
                   [e_var (varn_name "counters"); e_var (varn_name "tmp");
                    e_cast (cast_unsigned 32)
                      (e_acc
                         (e_acc (e_acc (e_var (varn_name "h")) "h") "row")
                         "t")]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "register" "write")
                      [e_var (varn_name "counters");
                       e_cast (cast_unsigned 32)
                         (e_acc
                            (e_acc (e_acc (e_var (varn_name "h")) "h") "row")
                            "t");
                       e_binop (e_var (varn_name "tmp")) binop_add
                         (e_v
                            (v_bit
                               ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                                 F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                                 F; T],32)))]))
                (stmt_ass
                   (lval_field
                      (lval_field
                         (lval_field (lval_varname (varn_name "h")) "h")
                         "row") "t")
                   (e_cast (cast_unsigned 16) (e_var (varn_name "tmp"))))))),
     [])],[(varn_name "counters",tau_ext,NONE)],[],[])],
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
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout); ("key",d_in); ("key_hmac",d_in)],
     ipsec_crypt_decrypt_aes_ctr);
    ("encrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout); ("key",d_in);
      ("key_hmac",d_in)],ipsec_crypt_encrypt_aes_ctr);
    ("encrypt_null",[("this",d_in); ("ipv4",d_inout); ("esp",d_inout)],
     ipsec_crypt_encrypt_null);
    ("decrypt_null",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout)],ipsec_crypt_decrypt_null)])],
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


val symb_exec8_astate_symb =
 rhs $ concl $ EVAL ``p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8;
 t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15;
 F; F; F; F; F; F; F; F;
 F; F; F; F; F; F; F; F;
 T; F; T; T; F; F; F; F],0)] ((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
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


val fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_ftymap_entries ^symb_exec8_ftymap”
val b_fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_b_ftymap_entries ^symb_exec8_blftymap”

val symb_exec8_ctx_tm = “(^fty_map', ^b_fty_map', ^symb_exec8_pblock_action_names_map)”
val symb_exec_ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "symb_exec_ctx" (mk_eq(mk_var("symb_exec_ctx", type_of symb_exec8_ctx_tm), symb_exec8_ctx_tm))

(* TODO: Not needed? *)
val symb_exec8_pblock_map = #2 $ p4Syntax.dest_actx symb_exec8_actx;
val symb_exec_pblock_map_def = hd $ Defn.eqns_of $ Defn.mk_defn "pblock_map" (mk_eq(mk_var("pblock_map", type_of symb_exec8_pblock_map), symb_exec8_pblock_map))

(* symb_exec: *)
(* Parameter assignment for debugging: *)
val debug_flag = true;
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec8_actx
val (fty_map, b_fty_map, pblock_action_names_map) = (symb_exec8_ftymap, symb_exec8_blftymap, symb_exec8_pblock_action_names_map)
val const_actions_tables = []
val path_cond_defs = [symb_exec_ctx_def, symb_exec_pblock_map_def]
val init_astate = symb_exec8_astate_symb
val stop_consts_rewr = [“v1model_register_construct_inner”, “v1model_register_read_inner”, “v1model_register_write_inner”]
val stop_consts_never = []
val thms_to_add = []
val path_cond = ASSUME “T”
val p4_is_finished_alt_opt = NONE
val n_max = 150;
val postcond = “(\s. T):v1model_ascope astate -> bool”;
val fuel = 1;
val postcond_rewr_thms = []
val postcond_simpset = pure_ss

val time_start = Time.now(); (*
val p4_symb_exec_fun = (p4_symb_exec 1)
*)
val contract_thm = p4_symb_exec_prove_contract debug_flag arch_ty (def_term ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never [] path_cond p4_is_finished_alt_opt n_max postcond postcond_rewr_thms postcond_simpset;

val _ = print (String.concat ["Total time consumption: ",
                              (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
                              " ms\n"]);

val _ = export_theory ();
