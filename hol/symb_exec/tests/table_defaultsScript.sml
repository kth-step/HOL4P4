Theory table_defaults
Ancestors
  p4 p4_symb_exec[qualified]
Libs
  liteLib p4_testLib p4_symb_execLib

(* Tables with symbolic entries: tnodef with the implicit NoAction default, texpr with the
 * default set_port(9w2 + 9w3) and tok with two actions. Imported with --mode symbolic; the
 * empty tables of the initial state were replaced by tok_tbl, texpr_tbl and tnodef_tbl. *)

val table_defaults_blftymap = ``[("MyParser",[]); ("MyVerifyChecksum",[]);
 ("MyIngress",[(funn_name "set_port",[p_tau_bit 9],p_tau_bot)]);
 ("MyEgress",[]); ("MyComputeChecksum",[]); ("MyDeparser",[])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val table_defaults_ftymap = ``[(funn_ext "Checksum16" "get",[p_tau_par "D9"],p_tau_bit 16);
 (funn_inst "Checksum16",[],p_tau_ext "Checksum16");
 (funn_inst "action_selector",[p_tau_bit 32; p_tau_bit 32; p_tau_bit 32],
  p_tau_ext "action_selector");
 (funn_inst "action_profile",[p_tau_bit 32],p_tau_ext "action_profile");
 (funn_ext "register" "write",[p_tau_bit 32; p_tau_par "T5"],p_tau_bot);
 (funn_ext "register" "read",[p_tau_par "T5"; p_tau_bit 32],p_tau_bot);
 (funn_inst "register",[p_tau_bit 32],p_tau_ext "register");
 (funn_ext "direct_meter" "read",[p_tau_par "T4"],p_tau_bot);
 (funn_inst "direct_meter",[p_tau_bit 32],p_tau_ext "direct_meter");
 (funn_ext "meter" "execute_meter",[p_tau_bit 32; p_tau_par "T3"],p_tau_bot);
 (funn_inst "meter",[p_tau_bit 32; p_tau_bit 32],p_tau_ext "meter");
 (funn_ext "direct_counter" "count",[],p_tau_bot);
 (funn_inst "direct_counter",[p_tau_bit 32],p_tau_ext "direct_counter");
 (funn_ext "counter" "count",[p_tau_bit 32],p_tau_bot);
 (funn_inst "counter",[p_tau_bit 32; p_tau_bit 32],p_tau_ext "counter");
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
 (funn_ext "" "static_assert",[p_tau_bool],p_tau_bool);
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
  [p_tau_par "O"; p_tau_bit 32; p_tau_par "T8"; p_tau_par "D"; p_tau_par "M"],
  p_tau_bot);
 (funn_ext "" "verify_checksum",
  [p_tau_bool; p_tau_par "T10"; p_tau_par "O11"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "update_checksum",
  [p_tau_bool; p_tau_par "T12"; p_tau_par "O13"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "verify_checksum_with_payload",
  [p_tau_bool; p_tau_par "T14"; p_tau_par "O15"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "update_checksum_with_payload",
  [p_tau_bool; p_tau_par "T16"; p_tau_par "O17"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "resubmit",[p_tau_par "T18"],p_tau_bot);
 (funn_ext "" "recirculate",[p_tau_par "T19"],p_tau_bot);
 (funn_ext "" "clone",[p_tau_bit 32; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "clone3",[p_tau_bit 32; p_tau_bit 32; p_tau_par "T20"],
  p_tau_bot); (funn_ext "" "truncate",[p_tau_bit 32],p_tau_bot);
 (funn_ext "" "assert",[p_tau_bool],p_tau_bot);
 (funn_ext "" "assume",[p_tau_bool],p_tau_bot);
 (funn_ext "" "log_msg",[p_tau_bot; p_tau_par "T21"],p_tau_bot)]:((funn, (p_tau list # p_tau)) alist)``;

val table_defaults_pblock_action_names_map = ``[("MyParser",[]); ("MyVerifyChecksum",[]);
 ("MyIngress",
  [("MyIngress.tok",["set_port"; "NoAction"]);
   ("MyIngress.texpr",["set_port"]);
   ("MyIngress.tnodef",["set_port"; "NoAction"])]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:((string, ((string, string list) alist)) alist)``;

val table_defaults_actx = ``([arch_block_inp;
  arch_block_pbl "MyParser"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "MyVerifyChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyIngress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_ffbl "traffic_manager";
  arch_block_pbl "MyEgress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyComputeChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyDeparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("MyParser",pbl_type_parser,
   [("b",d_none); ("hdr",d_out); ("meta",d_inout); ("sm",d_inout)],
   [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [],
   [("start",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "b"); e_acc (e_var (varn_name "hdr")) "h"]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
  ("MyVerifyChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyIngress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyIngress",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_app "MyIngress.tnodef"
             [e_acc (e_acc (e_var (varn_name "hdr")) "h") "f"])
          (stmt_seq
             (stmt_app "MyIngress.texpr"
                [e_acc (e_acc (e_var (varn_name "hdr")) "h") "f"])
             (stmt_app "MyIngress.tok"
                [e_acc (e_acc (e_var (varn_name "hdr")) "h") "f"]))),[]);
    ("set_port",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table$"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit$"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit$")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "sm")) "egress_spec")
             (e_var (varn_name "p"))) (stmt_ret (e_v v_bot))),
     [("from_table$",d_in); ("hit$",d_in); ("p",d_none)])],[],[],
   [("MyIngress.tok",[mk_exact],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("MyIngress.texpr",[mk_exact],"set_port",
     [e_v (v_bool T); e_v (v_bool F);
      e_v (v_bit ([F; F; F; F; F; F; T; F; T],9))]);
    ("MyIngress.tnodef",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)])]);
  ("MyEgress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyEgress",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyComputeChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyComputeChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyDeparser",pbl_type_control,[("b",d_none); ("hdr",d_in)],
   [("MyDeparser",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "packet_out" "emit")
             [e_var (varn_name "b"); e_acc (e_var (varn_name "hdr")) "h"])),
     [])],[],[],[])],[("postparser",ffblock_ff v1model_postparser);
  ("traffic_manager",ffblock_ff (v1model_traffic_manager random_oracle))],
 v1model_input_f random_oracle 0
   (v_struct [("h",v_header F [("f",v_bit ([F; F; F; F; F; F; F; F],8))])],
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
      ("algo",d_none)],v1model_update_checksum);
    ("hash",
     [("result",d_out); ("algo",d_none); ("base",d_in); ("data",d_in);
      ("max",d_in)],v1model_hash random_oracle)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],
      register_construct random_oracle),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],
     register_read random_oracle);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)]);
  ("counter",
   SOME
     ([("this",d_out); ("size",d_none); ("type",d_none)],counter_construct),
   [("count",[("this",d_in); ("index",d_in)],counter_count)]);
  ("ipsec_crypt",SOME ([("this",d_out)],ipsec_crypt_construct),
   [("decrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout); ("key",d_in); ("key_hmac",d_in)],
     ipsec_crypt_decrypt_aes_ctr random_oracle);
    ("encrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout); ("key",d_in);
      ("key_hmac",d_in)],ipsec_crypt_encrypt_aes_ctr random_oracle);
    ("encrypt_null",[("this",d_in); ("ipv4",d_inout); ("esp",d_inout)],
     ipsec_crypt_encrypt_null random_oracle);
    ("decrypt_null",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout)],ipsec_crypt_decrypt_null random_oracle)])],
 [("NoAction",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table$"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit$"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit$")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; F],32)))]))
        stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
   [("from_table$",d_in); ("hit$",d_in)])],v1model_get_oracle_index,
 v1model_set_oracle_index,random_oracle):v1model_ascope actx``;

val table_defaults_astate = ``((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
  [("MyIngress.tok",tok_tbl); ("MyIngress.texpr",texpr_tbl); ("MyIngress.tnodef",tnodef_tbl)],0),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool F); ("miss",v_bool T);
       ("action_run",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F],32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate``;


val p = “p:bool list”;
val init_astate = rhs $ concl $ EVAL “p4_append_input_list [(^p,0)] ^table_defaults_astate”;
val ctx = table_defaults_actx;
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "ctx" (mk_eq(mk_comb (mk_var ("ctx", mk_fun_ty “:random_oracle” (type_of ctx)), “random_oracle:random_oracle”), ctx));
val ctx_data = def_thm ctx_def;
val fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_ftymap_entries ^table_defaults_ftymap”;
val b_fty_map' = optionSyntax.dest_some $ rhs $ concl $ EVAL “deparameterise_b_ftymap_entries ^table_defaults_blftymap”;
val ty_ctx_tm = “(^fty_map', ^b_fty_map', ^table_defaults_pblock_action_names_map)”;
val ty_ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "ty_ctx" (mk_eq(mk_var("ty_ctx", type_of ty_ctx_tm), ty_ctx_tm));
val pblock_map_tm = #2 $ p4Syntax.dest_actx ctx;
val pblock_map_def = hd $ Defn.eqns_of $ Defn.mk_defn "pblock_map" (mk_eq(mk_var("pblock_map", type_of pblock_map_tm), pblock_map_tm));
fun wf_tm (name, var) = “v1model_tbl_is_well_formed ^(lhs $ concl ty_ctx_def) ^(lhs $ concl pblock_map_def) (^(stringSyntax.fromMLstring name), ^var)”;
val ctrl = #4 $ p4_v1modelLib.dest_v1model_ascope $ #4 $ p4Syntax.dest_aenv $ #1 $ p4Syntax.dest_astate init_astate;
val tbl_vars = map (pairSyntax.dest_pair) $ fst $ listSyntax.dest_list ctrl;
val wf_conjs = map (fn (n, v) => wf_tm (stringSyntax.fromHOLstring n, v)) tbl_vars;
val path_cond = ASSUME (list_mk_conj ((“8 <= LENGTH ^p”)::wf_conjs));
val debug_flag = false;
val arch_ty = p4_v1modelLib.v1model_arch_ty;
val (fty_map, b_fty_map, pblock_action_names_map) = (table_defaults_ftymap, table_defaults_blftymap, table_defaults_pblock_action_names_map);
val path_cond_defs = [ty_ctx_def, pblock_map_def];
val end_point = “p4_finished:v1model_ascope astate -> bool”;
val postcond = “(\s. T):v1model_ascope astate -> bool”;

val contract_thm = p4_symb_exec_prove_contract debug_flag arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) [] path_cond_defs init_astate [] [] [] path_cond end_point 300 postcond [] pure_ss;
