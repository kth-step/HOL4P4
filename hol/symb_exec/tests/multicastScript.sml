Theory multicast
Ancestors
  p4 p4_v1model[qualified] p4_symb_exec[qualified]
Libs
  liteLib p4_symb_execSyntax p4_symb_execLib

(* A multicast group of two copies with a free copy ordering, written by hand for:

#include <core.p4>
#include <v1model.p4>

header h_t {
    bit<8> a;
    bit<8> b;
}

struct metadata { }

struct headers {
    h_t h;
}

register<bit<8>>(4) reg;

parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    state start {
        packet.extract(hdr.h);
        transition accept;
    }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    apply {
        sm.mcast_grp = 1;
        reg.write(0, 0);
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    apply {
        bit<8> x;
        reg.read(x, 0);
        reg.write(0, x + 1);
        if (x == 0) { mark_to_drop(sm); }
    }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.h);
    }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;

with group 1 = [(port 1, rid 0); (port 2, rid 0)] in the control plane *)

val multicast_blftymap = ``[("MyParser",[]); ("MyVerifyChecksum",[]); ("MyIngress",[]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val multicast_ftymap = ``[(funn_ext "Checksum16" "get",[p_tau_par "D9"],p_tau_bit 16);
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

val multicast_pblock_action_names_map = ``[("MyParser",[]); ("MyVerifyChecksum",[]); ("MyIngress",[]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:((string, ((string, string list) alist)) alist)``;

(* The copy ordering of the traffic manager, a parameter of the context *)
val order_f = “order_f:num -> (num # num) list -> (num # num) list”;

val multicast_egress = “stmt_seq stmt_empty
  (stmt_block [(varn_name "x",tau_bit 8,NONE)]
     (stmt_seq
        (stmt_ass lval_null
           (e_call (funn_ext "register" "read")
              [e_var (varn_name "reg"); e_var (varn_name "x");
               e_v (v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],32))]))
        (stmt_seq
           (stmt_ass lval_null
              (e_call (funn_ext "register" "write")
                 [e_var (varn_name "reg");
                  e_v (v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],32));
                  e_binop (e_var (varn_name "x")) binop_add
                    (e_v (v_bit ([F; F; F; F; F; F; F; T],8)))]))
           (stmt_cond
              (e_binop (e_var (varn_name "x")) binop_eq
                 (e_v (v_bit ([F; F; F; F; F; F; F; F],8))))
              (stmt_block []
                 (stmt_ass lval_null
                    (e_call (funn_ext "" "mark_to_drop")
                       [e_var (varn_name "sm")]))) stmt_empty))))”;

val multicast_actx = ``([arch_block_inp;
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
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_ffbl "next_copy"; arch_block_out],
 [("MyParser",pbl_type_parser,
   [("packet",d_none); ("hdr",d_out); ("meta",d_inout); ("sm",d_inout)],
   [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [],
   [("start",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "h"]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
  ("MyVerifyChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyIngress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyIngress",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "sm")) "mcast_grp")
             (e_v (v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],16))))
          (stmt_ass lval_null
             (e_call (funn_ext "register" "write")
                [e_var (varn_name "reg");
                 e_v (v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],32));
                 e_v (v_bit ([F; F; F; F; F; F; F; F],8))]))),[])],
   [],[],[]);
  ("MyEgress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("sm",d_inout)],
   [("MyEgress",
     ^multicast_egress,[])],[],
   [],[]);
  ("MyComputeChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyComputeChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyDeparser",pbl_type_control,[("packet",d_none); ("hdr",d_in)],
   [("MyDeparser",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "packet_out" "emit")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "h"])),[])],[],[],[])],
 ^(p4_v1modelLib.v1model_ffblock_map_gen order_f),
 v1model_input_f random_oracle 1
   (v_struct
      [("h",
        v_header F
          [("a",v_bit ([F; F; F; F; F; F; F; F],8));
           ("b",v_bit ([F; F; F; F; F; F; F; F],8))])],v_struct []),
 v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
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

val multicast_astate = ``((0,[],[],1,
  [(0,
    INR
      (v1model_v_ext_register
         (v1model_register_construct_inner 4 8 0 random_oracle)))],
  [("parseError",
    v_bit
      ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
        F; F; F; F; F; F; F; F; F],32))],([],[(1,[(1,0); (2,0)])]),32),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool F); ("miss",v_bool T);
       ("action_run",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F],32))],NONE);
   (varn_name "reg",v_ext_ref 0,NONE)]],arch_frame_list_empty,status_running):v1model_ascope astate``;


val p = “p:bool list”;
val init_astate = rhs $ concl $ computeLib.RESTR_EVAL_CONV [“v1model_register_construct_inner”] “p4_append_input_list [(^p,0)] ^multicast_astate”;
val ctx = multicast_actx;
val random_oracle = “random_oracle:random_oracle”;
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "ctx" (mk_eq (list_mk_comb (mk_var ("ctx", type_of random_oracle --> type_of order_f --> type_of ctx), [random_oracle, order_f]), ctx));
val ctx_data = def_thm ctx_def;
val debug_flag = false;
val arch_ty = p4_v1modelLib.v1model_arch_ty;
val (fty_map, b_fty_map, pblock_action_names_map) = (multicast_ftymap, multicast_blftymap, multicast_pblock_action_names_map);
val const_actions_tables = [];
val path_cond_defs = [];
(* The register contents are evaluated, so each copy reads what the previous one wrote *)
val stop_consts_rewr = [];
val stop_consts_never = [];
val thms_to_add = [];
val path_cond = ASSUME “16 <= LENGTH ^p”;
val end_point = “p4_finished:v1model_ascope astate -> bool”;
val n_max = 300;
val postcond_rewr_thms = [p4_symb_execTheory.packet_has_port_def];
fun prove_contract ctx_data init_astate postcond =
 p4_symb_exec_prove_contract debug_flag arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond end_point n_max postcond postcond_rewr_thms pure_ss;

(* Each ordering of the copies is a path: the first copy is dropped, the other leaves *)
val postcond = “(\s. packet_has_port s 1 \/ packet_has_port s 2):v1model_ascope astate -> bool”;
val contract_thm = prove_contract ctx_data init_astate postcond;

(* The ordering with port 2 first leaves on port 1 *)
val _ =
 (prove_contract ctx_data init_astate “(\s. packet_has_port s 2):v1model_ascope astate -> bool”;
  raise Fail "a postcondition that fails for one ordering was accepted")
 handle HOL_ERR e => if #origin_function e = "EQT_ELIM" then () else raise HOL_ERR e;

(* The precondition assumes that the ordering permutes the copies, before the initial state *)
val s = mk_var ("s", type_of init_astate);
val wf_ordering = mk_comb (prim_mk_const {Thy = "p4_symb_exec", Name = "v1model_wf_ordering"}, order_f);
val expected_contract = mk_p4_contract_at (mk_abs (s, mk_conj (mk_conj (concl path_cond, wf_ordering), mk_eq (s, init_astate))), lhs $ snd $ strip_forall $ concl ctx_def, end_point, postcond);
val _ =
 if null (hyp contract_thm) andalso aconv (concl contract_thm) expected_contract
 then ()
 else raise mk_HOL_ERR "multicast" "contract_thm" "unexpected statement or hypotheses";

(* An empty group has one ordering, and the packet gives no output *)
val empty_group_astate = subst [“[(1, [(1, 0); (2, 0)])]:(num, (num # num) list) alist” |-> “[(1, [])]:(num, (num # num) list) alist”] init_astate;
val _ = prove_contract ctx_data empty_group_astate “(\s. output_ports s = []):v1model_ascope astate -> bool”;

(* MyEgress of spec_ctx: sm.egress_spec = (bit<9>) (hdr.h.a ++ hdr.h.b); *)
val spec_egress = “stmt_seq stmt_empty
  (stmt_ass (lval_field (lval_varname (varn_name "sm")) "egress_spec")
     (e_cast (cast_unsigned 9)
        (e_concat (e_acc (e_acc (e_var (varn_name "hdr")) "h") "a")
           (e_acc (e_acc (e_var (varn_name "hdr")) "h") "b"))))”;
val spec_ctx = subst [multicast_egress |-> spec_egress] ctx;
val spec_ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "spec_ctx" (mk_eq (list_mk_comb (mk_var ("spec_ctx", type_of random_oracle --> type_of order_f --> type_of spec_ctx), [random_oracle, order_f]), spec_ctx));

(* next_copy branches on the drop of the first copy, and the second copy has the same egress_spec *)
val _ = prove_contract (def_thm spec_ctx_def) init_astate “(\s. output_ports s = [] \/ is_perm (output_ports s) [1; 2]):v1model_ascope astate -> bool”;
val _ =
 (prove_contract (def_thm spec_ctx_def) init_astate “(\s. is_perm (output_ports s) [1; 2]):v1model_ascope astate -> bool”;
  raise Fail "a postcondition that fails when the copies are dropped was accepted")
 handle HOL_ERR e => if #origin_function e = "EQT_ELIM" then () else raise HOL_ERR e;

val _ = save_thm ("multicast_contract", contract_thm);
