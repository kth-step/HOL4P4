Theory decompose_varbit
Ancestors
  p4 p4_v1model[qualified] p4_symb_exec[qualified]
Libs
  liteLib p4_symb_execSyntax p4_symb_execLib

(* Decomposition over states with extracted varbits of widths 0, 8 and 16, imported with --mode symbolic from:

#include <core.p4>
#include <v1model.p4>

header l_t {
    bit<8> len;
}

header v_t {
    bit<8> a;
    varbit<16> v;
}

struct metadata { }

struct headers {
    l_t l;
    v_t h;
}

parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    state start {
        packet.extract(hdr.l);
        transition select (hdr.l.len) {
            1: parse8;
            2: parse16;
            default: accept;
        }
    }
    state parse8 {
        packet.extract(hdr.h, 8);
        transition accept;
    }
    state parse16 {
        packet.extract(hdr.h, 16);
        transition accept;
    }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    apply {
        sm.egress_spec = 1;
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    apply {
        if (hdr.h.isValid()) {
            if (hdr.h.a == 0) { mark_to_drop(sm); }
        }
    }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.l);
        packet.emit(hdr.h);
    }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
*)

val decompose_varbit_blftymap = ``[("MyParser",[]); ("MyVerifyChecksum",[]); ("MyIngress",[]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val decompose_varbit_ftymap = ``[(funn_ext "Checksum16" "get",[p_tau_par "D9"],p_tau_bit 16);
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

val decompose_varbit_pblock_action_names_map = ``[("MyParser",[]); ("MyVerifyChecksum",[]); ("MyIngress",[]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:((string, ((string, string list) alist)) alist)``;

val decompose_varbit_actx = ``([arch_block_inp;
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
    [e_var (varn_name "b"); e_var (varn_name "hdr")];
  arch_block_ffbl "next_copy"; arch_block_out],
 [("MyParser",pbl_type_parser,
   [("packet",d_none); ("hdr",d_out); ("meta",d_inout); ("sm",d_inout)],
   [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [],
   [("start",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "l"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",e_acc (e_acc (e_var (varn_name "hdr")) "l") "len")])
             [([s_sing (v_bit ([F; F; F; F; F; F; F; T],8))],"parse8");
              ([s_sing (v_bit ([F; F; F; F; F; F; T; F],8))],"parse16")]
             "accept")));
    ("parse8",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract_varbit")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "h";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; T; F; F; F],32))]))
       (stmt_trans (e_v (v_str "accept"))));
    ("parse16",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract_varbit")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "h";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; T; F; F; F; F],32))]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
  ("MyVerifyChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyIngress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyIngress",
     stmt_seq stmt_empty
       (stmt_ass (lval_field (lval_varname (varn_name "sm")) "egress_spec")
          (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9)))),[])],[],[],[]);
  ("MyEgress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyEgress",
     stmt_seq stmt_empty
       (stmt_cond
          (e_call (funn_ext "header" "isValid")
             [e_acc (e_var (varn_name "hdr")) "h"])
          (stmt_block []
             (stmt_cond
                (e_binop (e_acc (e_acc (e_var (varn_name "hdr")) "h") "a")
                   binop_eq (e_v (v_bit ([F; F; F; F; F; F; F; F],8))))
                (stmt_block []
                   (stmt_ass lval_null
                      (e_call (funn_ext "" "mark_to_drop")
                         [e_var (varn_name "sm")]))) stmt_empty)) stmt_empty),
     [])],[],[],[]);
  ("MyComputeChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyComputeChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyDeparser",pbl_type_control,[("packet",d_none); ("hdr",d_in)],
   [("MyDeparser",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "hdr")) "l"]))
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "hdr")) "h"]))),[])],[],[],[])],
 [("postparser",ffblock_ff v1model_postparser);
  ("traffic_manager",
   ffblock_ff (v1model_traffic_manager random_oracle (\(i:num) (l:(num # num) list). l)));
  ("next_copy",ffblock_ff (v1model_next_copy random_oracle))],
 v1model_input_f random_oracle 0
   (v_struct
      [("l",v_header F [("len",v_bit ([F; F; F; F; F; F; F; F],8))]);
       ("h",
        v_header F
          [("a",v_bit ([F; F; F; F; F; F; F; F],8));
           ("v",v_varbit ([],0) 16)])],v_struct []),v1model_output_f,
 v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f v1model_api_tdi,
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
    ("verify_checksum_with_payload",
     [("condition",d_in); ("data",d_in); ("checksum",d_in); ("algo",d_none)],
     v1model_verify_checksum_with_payload);
    ("update_checksum_with_payload",
     [("condition",d_in); ("data",d_in); ("checksum",d_inout);
      ("algo",d_none)],v1model_update_checksum_with_payload);
    ("hash",
     [("result",d_out); ("algo",d_none); ("base",d_in); ("data",d_in);
      ("max",d_in)],v1model_hash random_oracle);
    ("random",[("result",d_out); ("lo",d_in); ("hi",d_in)],
     v1model_random random_oracle);
    ("truncate",[("length",d_in)],v1model_truncate);
    ("assert",[("check",d_in)],v1model_assert);
    ("assume",[("check",d_in)],v1model_assume)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("extract_varbit",
     [("this",d_in); ("headerLvalue",d_out);
      ("variableFieldSizeInBits",d_in)],v1model_packet_in_extract_varbit);
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

val decompose_varbit_astate = ``((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],([],[]),0),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool F); ("miss",v_bool T);
       ("action_run",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F],32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate``;

val p = “p:bool list”;
val init_astate = rhs $ concl $ EVAL “p4_append_input_list [(^p,0)] ^decompose_varbit_astate”;
val ctx = decompose_varbit_actx;
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "ctx" (mk_eq(mk_comb (mk_var ("ctx", mk_fun_ty “:random_oracle” (type_of ctx)), “random_oracle:random_oracle”), ctx));
val ctx_data = def_thm ctx_def;
val debug_flag = false;
val arch_ty = p4_v1modelLib.v1model_arch_ty;
val (fty_map, b_fty_map, pblock_action_names_map) = (decompose_varbit_ftymap, decompose_varbit_blftymap, decompose_varbit_pblock_action_names_map);
val const_actions_tables = [];
val path_cond_defs = [];
val stop_consts_rewr = [];
val stop_consts_never = [];
val thms_to_add = [];
(* Every extract succeeds *)
val path_cond = ASSUME “LENGTH ^p = 32”;
val n_max = 300;

(* The cut: block 6 (MyEgress) is about to start, with varbits of widths 0, 8 and 16 on the three paths *)
val block_index_stop = “6:num”;
val end_point1 = “(\s. p4_block_next s ^block_index_stop):v1model_ascope astate -> bool”;
val p4_v1model_parser_wellformed_def = (fn defn => let val _ = Defn.save_defn defn in Defn.fetch_eqns defn end) $ get_v1model_wellformed_defs ctx init_astate block_index_stop;

(* 1. From the initial state to the cut *)
(* The traffic manager has set egress_port to 1 and egress_spec to 0 *)
val postcond1 = “(\s. p4_v1model_parser_wellformed s /\
                      p4_v1model_lookup_avar (lval_field (lval_varname (varn_name "standard_metadata")) "egress_port") s = SOME $ v_bit ([F; F; F; F; F; F; F; F; T],9) /\
                      p4_v1model_lookup_avar (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") s = SOME $ v_bit (REPLICATE 9 F,9) /\
                      p4_v1model_lookup_avar_validity (lval_field (lval_varname (varn_name "hdr")) "l") s = SOME T):v1model_ascope astate -> bool”;
val postcond_rewr_thms1 = [p4_symb_execTheory.p4_v1model_lookup_avar_def, p4_symb_execTheory.p4_v1model_lookup_avar_validity_def, p4Theory.lookup_lval_def, p4_coreTheory.v_map_to_scope_def];
val postcond_simpset1 = pure_ss++(p4_wellformed_ss p4_v1model_parser_wellformed_def);
val contract_thm1 = p4_symb_exec_prove_contract debug_flag arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond end_point1 n_max postcond1 postcond_rewr_thms1 postcond_simpset1;

(* 2. From the intermediate state, with any well-formed varbits in parsedHdr and hdr, to the end *)
val init_astate2 = get_intermediate_state postcond1 p4_v1model_parser_wellformed_def;
val path_cond2 = get_intermediate_path_cond postcond1 p4_v1model_parser_wellformed_def;
(* The path condition is wellformed_varbit 16 (bl, n) for the varbits of parsedHdr and hdr in init_astate2 *)
fun check_varbit_conj conj =
 let
  val (w, bl_n) = dest_wellformed_varbit conj
  val (bl, n) = pairSyntax.dest_pair bl_n
 in
  if term_eq w “16:num” andalso is_var bl andalso is_var n andalso can (find_term (term_eq (p4Syntax.mk_v_varbit (bl_n, w)))) init_astate2
  then [bl, n]
  else raise mk_HOL_ERR "decompose_varbit" "path_cond2" "unexpected varbit conjunct"
 end;
val varbit_vars = flatten $ map check_varbit_conj $ strip_conj $ concl path_cond2;
val _ =
 if length varbit_vars = 4 andalso length (op_mk_set aconv varbit_vars) = 4
 then ()
 else raise mk_HOL_ERR "decompose_varbit" "path_cond2" "unexpected path condition";
(* The predicate holds for the intermediate state, from its path condition *)
val _ = EQT_ELIM (SIMP_CONV (bool_ss++p4_wellformed_ss p4_v1model_parser_wellformed_def) [] (mk_imp (concl path_cond2, “p4_v1model_parser_wellformed ^init_astate2”)));
val end_point = “p4_finished:v1model_ascope astate -> bool”;
val postcond = “(\s. packet_has_port s 1 \/ packet_dropped s):v1model_ascope astate -> bool”;
val postcond_rewr_thms = [p4_symb_execTheory.packet_has_port_def, p4_symb_execTheory.packet_dropped_def];
val contract_thm2 = p4_symb_exec_prove_contract debug_flag arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate2 stop_consts_rewr stop_consts_never thms_to_add path_cond2 end_point n_max postcond postcond_rewr_thms pure_ss;

(* 3. The combined contract: from the initial state to the end *)
val combined_contract = p4_combine_contracts contract_thm1 contract_thm2 p4_v1model_parser_wellformed_def;

(* The statements, built from the inputs, without hypotheses *)
fun expected_contract (pc, astate, ep, post) =
 let
  val s = mk_var ("s", type_of astate)
 in
  mk_p4_contract_at (mk_abs (s, mk_conj (concl pc, mk_eq (s, astate))), lhs $ snd $ strip_forall $ concl ctx_def, ep, post)
 end;
fun check_contract name thm expected =
 if null (hyp thm) andalso aconv (concl thm) expected
 then ()
 else raise mk_HOL_ERR "decompose_varbit" name "unexpected statement or hypotheses";
val _ = check_contract "contract_thm1" contract_thm1 (expected_contract (path_cond, init_astate, end_point1, postcond1));
val _ = check_contract "contract_thm2" contract_thm2 (expected_contract (path_cond2, init_astate2, end_point, postcond));
val _ = check_contract "combined_contract" combined_contract (expected_contract (path_cond, init_astate, end_point, postcond));
