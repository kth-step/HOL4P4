open HolKernel boolLib liteLib simpLib Parse bossLib;
open p4_testLib;

open p4_symb_execLib;

val _ = new_theory "basic";

val basic_blftymap = ``[("MyParser",[]); ("MyVerifyChecksum",[]);
 ("MyIngress",
  [(funn_name "drop",[],p_tau_bot);
   (funn_name "send_to_controller",[p_tau_bit 16],p_tau_bot);
   (funn_name "l2_forward",[p_tau_bit 48; p_tau_bit 9],p_tau_bot);
   (funn_name "l3_forward",[p_tau_bit 9],p_tau_bot);
   (funn_name "esp_decrypt_aes_ctr",
    [p_tau_bit 160; p_tau_bit 128; p_tau_bit 32],p_tau_bot);
   (funn_name "esp_decrypt_null",[p_tau_bit 32],p_tau_bot);
   (funn_name "esp_encrypt_aes_ctr",
    [p_tau_bit 160; p_tau_bit 128; p_tau_bit 32; p_tau_bit 32; p_tau_bit 32;
     p_tau_bit 32; p_tau_bit 32; p_tau_bit 32],p_tau_bot);
   (funn_name "esp_encrypt_null",
    [p_tau_bit 32; p_tau_bit 32; p_tau_bit 32; p_tau_bit 32; p_tau_bit 32;
     p_tau_bit 32],p_tau_bot);
   (funn_name "add_spd_mark",[p_tau_bit 4],p_tau_bot);
   (funn_name "clone_packet",[],p_tau_bot);
   (funn_name "sadb_acquire",[],p_tau_bot)]); ("MyEgress",[]);
 ("MyComputeChecksum",[]); ("MyDeparser",[])]:(string, ((funn, (p_tau list # p_tau)) alist)) alist``;

val basic_ftymap = ``[(funn_ext "ipsec_crypt" "decrypt_null",
  [p_tau_xtl struct_ty_header
     [("version",p_tau_bit 4); ("ihl",p_tau_bit 4); ("diffserv",p_tau_bit 8);
      ("totalLen",p_tau_bit 16); ("identification",p_tau_bit 16);
      ("flags",p_tau_bit 3); ("fragOffset",p_tau_bit 13);
      ("ttl",p_tau_bit 8); ("protocol",p_tau_bit 8);
      ("hdrChecksum",p_tau_bit 16); ("srcAddr",p_tau_bit 32);
      ("dstAddr",p_tau_bit 32)];
   p_tau_xtl struct_ty_header
     [("spi",p_tau_bit 32); ("sequenceNumber",p_tau_bit 32)];
   p_tau_xtl struct_ty_struct
     [("ingress_port",p_tau_bit 9); ("egress_spec",p_tau_bit 9);
      ("egress_port",p_tau_bit 9); ("instance_type",p_tau_bit 32);
      ("packet_length",p_tau_bit 32); ("enq_timestamp",p_tau_bit 32);
      ("enq_qdepth",p_tau_bit 19); ("deq_timedelta",p_tau_bit 32);
      ("deq_qdepth",p_tau_bit 19); ("ingress_global_timestamp",p_tau_bit 48);
      ("egress_global_timestamp",p_tau_bit 48); ("mcast_grp",p_tau_bit 16);
      ("egress_rid",p_tau_bit 16); ("checksum_error",p_tau_bit 1);
      ("parser_error",p_tau_bit 32); ("priority",p_tau_bit 3)]],p_tau_bot);
 (funn_ext "ipsec_crypt" "encrypt_null",
  [p_tau_xtl struct_ty_header
     [("version",p_tau_bit 4); ("ihl",p_tau_bit 4); ("diffserv",p_tau_bit 8);
      ("totalLen",p_tau_bit 16); ("identification",p_tau_bit 16);
      ("flags",p_tau_bit 3); ("fragOffset",p_tau_bit 13);
      ("ttl",p_tau_bit 8); ("protocol",p_tau_bit 8);
      ("hdrChecksum",p_tau_bit 16); ("srcAddr",p_tau_bit 32);
      ("dstAddr",p_tau_bit 32)];
   p_tau_xtl struct_ty_header
     [("spi",p_tau_bit 32); ("sequenceNumber",p_tau_bit 32)]],p_tau_bot);
 (funn_ext "ipsec_crypt" "encrypt_aes_ctr",
  [p_tau_xtl struct_ty_header
     [("version",p_tau_bit 4); ("ihl",p_tau_bit 4); ("diffserv",p_tau_bit 8);
      ("totalLen",p_tau_bit 16); ("identification",p_tau_bit 16);
      ("flags",p_tau_bit 3); ("fragOffset",p_tau_bit 13);
      ("ttl",p_tau_bit 8); ("protocol",p_tau_bit 8);
      ("hdrChecksum",p_tau_bit 16); ("srcAddr",p_tau_bit 32);
      ("dstAddr",p_tau_bit 32)];
   p_tau_xtl struct_ty_header
     [("spi",p_tau_bit 32); ("sequenceNumber",p_tau_bit 32)]; p_tau_bit 160;
   p_tau_bit 128],p_tau_bot);
 (funn_ext "ipsec_crypt" "decrypt_aes_ctr",
  [p_tau_xtl struct_ty_header
     [("version",p_tau_bit 4); ("ihl",p_tau_bit 4); ("diffserv",p_tau_bit 8);
      ("totalLen",p_tau_bit 16); ("identification",p_tau_bit 16);
      ("flags",p_tau_bit 3); ("fragOffset",p_tau_bit 13);
      ("ttl",p_tau_bit 8); ("protocol",p_tau_bit 8);
      ("hdrChecksum",p_tau_bit 16); ("srcAddr",p_tau_bit 32);
      ("dstAddr",p_tau_bit 32)];
   p_tau_xtl struct_ty_header
     [("spi",p_tau_bit 32); ("sequenceNumber",p_tau_bit 32)];
   p_tau_xtl struct_ty_struct
     [("ingress_port",p_tau_bit 9); ("egress_spec",p_tau_bit 9);
      ("egress_port",p_tau_bit 9); ("instance_type",p_tau_bit 32);
      ("packet_length",p_tau_bit 32); ("enq_timestamp",p_tau_bit 32);
      ("enq_qdepth",p_tau_bit 19); ("deq_timedelta",p_tau_bit 32);
      ("deq_qdepth",p_tau_bit 19); ("ingress_global_timestamp",p_tau_bit 48);
      ("egress_global_timestamp",p_tau_bit 48); ("mcast_grp",p_tau_bit 16);
      ("egress_rid",p_tau_bit 16); ("checksum_error",p_tau_bit 1);
      ("parser_error",p_tau_bit 32); ("priority",p_tau_bit 3)];
   p_tau_bit 160; p_tau_bit 128],p_tau_bot);
 (funn_inst "ipsec_crypt",[],p_tau_ext "ipsec_crypt");
 (funn_ext "Checksum16" "get",[p_tau_par "D9"],p_tau_bit 16);
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
  p_tau_bot); (funn_ext "" "resubmit",[p_tau_par "T18"],p_tau_bot);
 (funn_ext "" "recirculate",[p_tau_par "T19"],p_tau_bot);
 (funn_ext "" "clone",[p_tau_par "CloneType"; p_tau_bit 32],p_tau_bot);
 (funn_ext "" "clone3",
  [p_tau_par "CloneType"; p_tau_bit 32; p_tau_par "T20"],p_tau_bot);
 (funn_ext "" "truncate",[p_tau_bit 32],p_tau_bot);
 (funn_ext "" "assert",[p_tau_bool],p_tau_bot);
 (funn_ext "" "assume",[p_tau_bool],p_tau_bot);
 (funn_ext "" "log_msg",[p_tau_bot; p_tau_par "T21"],p_tau_bot)]:((funn, (p_tau list # p_tau)) alist)``;

val basic_actx = ``([arch_block_inp;
  arch_block_pbl "MyParser"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "MyVerifyChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyIngress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyEgress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "MyComputeChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "MyDeparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("MyParser",pbl_type_parser,
   [("packet",d_none); ("hdr",d_out); ("meta",d_inout);
    ("standard_metadata",d_inout)],
   [("MyParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [],
   [("start",
     stmt_seq
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field (lval_varname (varn_name "meta")) "user_metadata")
                "spd_mark") (e_v (v_bit ([F; F; F; F],4))))
          (stmt_ass
             (lval_field
                (lval_field (lval_varname (varn_name "meta")) "user_metadata")
                "bypass") (e_v (v_bool F))))
       (stmt_trans (e_v (v_str "parse_ethernet"))));
    ("parse_ethernet",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "ethernet"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ethernet")
                    "etherType")])
             [([s_sing
                  (v_bit
                     ([F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F],16))],
               "parse_ipv4")] "accept")));
    ("parse_ipv4",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "ipv4"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "protocol")])
             [([s_sing (v_bit ([F; F; T; T; F; F; T; F],8))],"parse_esp")]
             "accept")));
    ("parse_esp",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "hdr")) "esp"]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
  ("MyVerifyChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyVerifyChecksum",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyIngress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
   [("MyIngress",
     stmt_seq
       (stmt_seq
          (stmt_seq
             (stmt_seq
                (stmt_seq
                   (stmt_seq
                      (stmt_ass lval_null
                         (e_call (funn_inst "ipsec_crypt")
                            [e_var (varn_name "ipsecCrypt")]))
                      (stmt_ass lval_null
                         (e_call (funn_inst "register")
                            [e_var (varn_name "counters");
                             e_v
                               (v_bit
                                  ([F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                                    F; F; F; F; F; F; F; T; F; F; F; F; F; F;
                                    F; F; F; F],32));
                             e_v
                               (v_bit
                                  ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                                    ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                                    ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                                    ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],
                                   32))])))
                   (stmt_ass (lval_varname (varn_name "notify_soft"))
                      (e_v (v_bool F))))
                (stmt_ass (lval_varname (varn_name "notify_hard"))
                   (e_v (v_bool F))))
             (stmt_ass (lval_varname (varn_name "do_drop")) (e_v (v_bool F))))
          (stmt_ass (lval_varname (varn_name "current_register"))
             (e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; F; F; F],32)))))
       (stmt_seq
          (stmt_cond
             (e_call (funn_ext "header" "isValid")
                [e_acc (e_var (varn_name "hdr")) "esp"])
             (stmt_block []
                (stmt_seq
                   (stmt_app "sad_decrypt"
                      [e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                         "srcAddr";
                       e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                         "dstAddr";
                       e_acc (e_acc (e_var (varn_name "hdr")) "esp") "spi"])
                   (stmt_app "forward"
                      [e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                         "dstAddr"])))
             (stmt_cond
                (e_call (funn_ext "header" "isValid")
                   [e_acc (e_var (varn_name "hdr")) "ipv4"])
                (stmt_block []
                   (stmt_seq
                      (stmt_app "spd"
                         [e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                            "dstAddr";
                          e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                            "protocol"])
                      (stmt_cond
                         (e_binop
                            (e_acc
                               (e_acc (e_var (varn_name "meta"))
                                  "user_metadata") "spd_mark") binop_eq
                            (e_v (v_bit ([F; F; F; T],4))))
                         (stmt_block []
                            (stmt_app "forward"
                               [e_acc
                                  (e_acc (e_var (varn_name "hdr")) "ipv4")
                                  "dstAddr"]))
                         (stmt_cond
                            (e_binop
                               (e_acc
                                  (e_acc (e_var (varn_name "meta"))
                                     "user_metadata") "spd_mark") binop_eq
                               (e_v (v_bit ([F; F; T; F],4))))
                            (stmt_block []
                               (stmt_seq
                                  (stmt_app "sad_encrypt"
                                     [e_acc
                                        (e_acc (e_var (varn_name "hdr"))
                                           "ipv4") "dstAddr"])
                                  (stmt_app "forward"
                                     [e_acc
                                        (e_acc (e_var (varn_name "hdr"))
                                           "ipv4") "dstAddr"]))) stmt_empty))))
                stmt_empty))
          (stmt_cond (e_var (varn_name "do_drop"))
             (stmt_block []
                (stmt_seq
                   (stmt_ass lval_null
                      (e_call (funn_ext "" "mark_to_drop")
                         [e_var (varn_name "standard_metadata")]))
                   (stmt_ret (e_v v_bot))))
             (stmt_cond (e_var (varn_name "notify_soft"))
                (stmt_block []
                   (stmt_seq
                      (stmt_ass lval_null
                         (e_call (funn_name "send_to_controller")
                            [e_v (v_bool F); e_v (v_bool ARB);
                             e_v
                               (v_bit
                                  ([F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                                    F; T],16))])) (stmt_ret (e_v v_bot))))
                (stmt_cond (e_var (varn_name "notify_hard"))
                   (stmt_block []
                      (stmt_seq
                         (stmt_ass lval_null
                            (e_call (funn_name "send_to_controller")
                               [e_v (v_bool F); e_v (v_bool ARB);
                                e_v
                                  (v_bit
                                     ([F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; T; F],16))]))
                         (stmt_ret (e_v v_bot)))) stmt_empty)))),[]);
    ("sadb_acquire",
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
                         F; F; F; F; F; F; F; F; F; F; F; T; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "standard_metadata"))
                   "egress_spec")
                (e_v (v_bit ([F; F; F; F; T; F; F; F; F],9))))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "header" "setValid")
                      [e_acc (e_var (varn_name "hdr")) "cpu_header"]))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr"))
                            "cpu_header") "reason")
                      (e_v
                         (v_bit
                            ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],
                             16))))
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr"))
                            "cpu_header") "timestamp")
                      (e_acc (e_var (varn_name "standard_metadata"))
                         "ingress_global_timestamp")))))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)]);
    ("clone_packet",
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
                         F; F; F; F; F; F; F; F; F; F; F; T; F; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_block
             [(varn_name "REPORT_MIRROR_SESSION_ID",tau_bit 32,NONE)]
             (stmt_seq
                (stmt_ass
                   (lval_varname (varn_name "REPORT_MIRROR_SESSION_ID"))
                   (e_v
                      (v_bit
                         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                           F; F; F; F; F; F; T; T; T; T; T; F; T; F; F],32))))
                (stmt_ass lval_null
                   (e_call (funn_ext "" "clone")
                      [e_v
                         (v_bit
                            ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                              F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],
                             32));
                       e_var (varn_name "REPORT_MIRROR_SESSION_ID")]))))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)]);
    ("add_spd_mark",
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
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field (lval_varname (varn_name "meta")) "user_metadata")
                "spd_mark") (e_var (varn_name "spd_mark")))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("spd_mark",d_none)]);
    ("esp_encrypt_null",
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
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_block [(varn_name "tmp",tau_bit 32,NONE)]
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "register" "read")
                      [e_var (varn_name "counters"); e_var (varn_name "tmp");
                       e_var (varn_name "register_index")]))
                (stmt_seq
                   (stmt_ass lval_null
                      (e_call (funn_ext "header" "setValid")
                         [e_acc (e_var (varn_name "hdr")) "esp"]))
                   (stmt_seq
                      (stmt_ass
                         (lval_field
                            (lval_field (lval_varname (varn_name "hdr"))
                               "esp") "spi") (e_var (varn_name "spi")))
                      (stmt_seq
                         (stmt_ass
                            (lval_field
                               (lval_field (lval_varname (varn_name "hdr"))
                                  "esp") "sequenceNumber")
                            (e_binop (e_var (varn_name "tmp")) binop_add
                               (e_v
                                  (v_bit
                                     ([F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; T],32)))))
                         (stmt_seq
                            (stmt_ass lval_null
                               (e_call
                                  (funn_ext "ipsec_crypt" "encrypt_null")
                                  [e_var (varn_name "ipsecCrypt");
                                   e_acc (e_var (varn_name "hdr")) "ipv4";
                                   e_acc (e_var (varn_name "hdr")) "esp"]))
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_field
                                        (lval_varname (varn_name "hdr"))
                                        "ipv4") "identification")
                                  (e_v
                                     (v_bit
                                        ([F; F; F; F; F; F; F; F; F; F; F; F;
                                          F; F; F; T],16))))
                               (stmt_seq
                                  (stmt_ass
                                     (lval_field
                                        (lval_field
                                           (lval_varname (varn_name "hdr"))
                                           "ipv4") "flags")
                                     (e_v (v_bit ([F; T; F],3))))
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_field
                                           (lval_field
                                              (lval_varname (varn_name "hdr"))
                                              "ipv4") "fragOffset")
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F],13))))
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_field
                                              (lval_field
                                                 (lval_varname
                                                    (varn_name "hdr")) "ipv4")
                                              "ttl")
                                           (e_v
                                              (v_bit
                                                 ([F; T; F; F; F; F; F; F],8))))
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_field
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name "hdr"))
                                                    "ipv4") "protocol")
                                              (e_v
                                                 (v_bit
                                                    ([F; F; T; T; F; F; T; F],
                                                     8))))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_field
                                                    (lval_field
                                                       (lval_varname
                                                          (varn_name "hdr"))
                                                       "ipv4") "srcAddr")
                                                 (e_var (varn_name "src")))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_field
                                                          (lval_varname
                                                             (varn_name "hdr"))
                                                          "ipv4") "dstAddr")
                                                    (e_var (varn_name "dst")))
                                                 (stmt_seq
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_ext
                                                             "register"
                                                             "write")
                                                          [e_var
                                                             (varn_name
                                                                "counters");
                                                           e_var
                                                             (varn_name
                                                                "register_index");
                                                           e_binop
                                                             (e_var
                                                                (varn_name
                                                                   "tmp"))
                                                             binop_add
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; T],32)))]))
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "notify_soft"))
                                                          (e_binop
                                                             (e_var
                                                                (varn_name
                                                                   "soft_packet_limit"))
                                                             binop_eq
                                                             (e_var
                                                                (varn_name
                                                                   "tmp"))))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "notify_hard"))
                                                             (e_binop
                                                                (e_var
                                                                   (varn_name
                                                                      "hard_packet_limit"))
                                                                binop_eq
                                                                (e_var
                                                                   (varn_name
                                                                      "tmp"))))
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "do_drop"))
                                                                (e_binop
                                                                   (e_var
                                                                      (varn_name
                                                                         "tmp"))
                                                                   binop_gt
                                                                   (e_var
                                                                      (varn_name
                                                                         "hard_packet_limit"))))
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "current_register"))
                                                                (e_var
                                                                   (varn_name
                                                                      "register_index"))))))))))))))))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("spi",d_none); ("src",d_none);
      ("dst",d_none); ("register_index",d_none);
      ("soft_packet_limit",d_none); ("hard_packet_limit",d_none)]);
    ("esp_encrypt_aes_ctr",
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
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_block [(varn_name "tmp",tau_bit 32,NONE)]
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "register" "read")
                      [e_var (varn_name "counters"); e_var (varn_name "tmp");
                       e_var (varn_name "register_index")]))
                (stmt_seq
                   (stmt_ass lval_null
                      (e_call (funn_ext "header" "setValid")
                         [e_acc (e_var (varn_name "hdr")) "esp"]))
                   (stmt_seq
                      (stmt_ass
                         (lval_field
                            (lval_field (lval_varname (varn_name "hdr"))
                               "esp") "spi") (e_var (varn_name "spi")))
                      (stmt_seq
                         (stmt_ass
                            (lval_field
                               (lval_field (lval_varname (varn_name "hdr"))
                                  "esp") "sequenceNumber")
                            (e_binop (e_var (varn_name "tmp")) binop_add
                               (e_v
                                  (v_bit
                                     ([F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; T],32)))))
                         (stmt_seq
                            (stmt_ass lval_null
                               (e_call
                                  (funn_ext "ipsec_crypt" "encrypt_aes_ctr")
                                  [e_var (varn_name "ipsecCrypt");
                                   e_acc (e_var (varn_name "hdr")) "ipv4";
                                   e_acc (e_var (varn_name "hdr")) "esp";
                                   e_var (varn_name "key");
                                   e_var (varn_name "key_hmac")]))
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_field
                                        (lval_varname (varn_name "hdr"))
                                        "ipv4") "identification")
                                  (e_v
                                     (v_bit
                                        ([F; F; F; F; F; F; F; F; F; F; F; F;
                                          F; F; F; T],16))))
                               (stmt_seq
                                  (stmt_ass
                                     (lval_field
                                        (lval_field
                                           (lval_varname (varn_name "hdr"))
                                           "ipv4") "flags")
                                     (e_v (v_bit ([F; T; F],3))))
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_field
                                           (lval_field
                                              (lval_varname (varn_name "hdr"))
                                              "ipv4") "fragOffset")
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F],13))))
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_field
                                              (lval_field
                                                 (lval_varname
                                                    (varn_name "hdr")) "ipv4")
                                              "ttl")
                                           (e_v
                                              (v_bit
                                                 ([F; T; F; F; F; F; F; F],8))))
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_field
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name "hdr"))
                                                    "ipv4") "protocol")
                                              (e_v
                                                 (v_bit
                                                    ([F; F; T; T; F; F; T; F],
                                                     8))))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_field
                                                    (lval_field
                                                       (lval_varname
                                                          (varn_name "hdr"))
                                                       "ipv4") "srcAddr")
                                                 (e_var (varn_name "src")))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_field
                                                          (lval_varname
                                                             (varn_name "hdr"))
                                                          "ipv4") "dstAddr")
                                                    (e_var (varn_name "dst")))
                                                 (stmt_seq
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_ext
                                                             "register"
                                                             "write")
                                                          [e_var
                                                             (varn_name
                                                                "counters");
                                                           e_var
                                                             (varn_name
                                                                "register_index");
                                                           e_binop
                                                             (e_var
                                                                (varn_name
                                                                   "tmp"))
                                                             binop_add
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; T],32)))]))
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "notify_soft"))
                                                          (e_binop
                                                             (e_var
                                                                (varn_name
                                                                   "soft_packet_limit"))
                                                             binop_eq
                                                             (e_var
                                                                (varn_name
                                                                   "tmp"))))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "notify_hard"))
                                                             (e_binop
                                                                (e_var
                                                                   (varn_name
                                                                      "hard_packet_limit"))
                                                                binop_eq
                                                                (e_var
                                                                   (varn_name
                                                                      "tmp"))))
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "do_drop"))
                                                                (e_binop
                                                                   (e_var
                                                                      (varn_name
                                                                         "tmp"))
                                                                   binop_gt
                                                                   (e_var
                                                                      (varn_name
                                                                         "hard_packet_limit"))))
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "current_register"))
                                                                (e_var
                                                                   (varn_name
                                                                      "register_index"))))))))))))))))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("key",d_none); ("key_hmac",d_none);
      ("spi",d_none); ("src",d_none); ("dst",d_none);
      ("register_index",d_none); ("soft_packet_limit",d_none);
      ("hard_packet_limit",d_none)]);
    ("esp_decrypt_null",
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
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "ipsec_crypt" "decrypt_null")
                   [e_var (varn_name "ipsecCrypt");
                    e_acc (e_var (varn_name "hdr")) "ipv4";
                    e_acc (e_var (varn_name "hdr")) "esp";
                    e_var (varn_name "standard_metadata")]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "header" "setInvalid")
                      [e_acc (e_var (varn_name "hdr")) "esp"]))
                (stmt_block [(varn_name "tmp",tau_bit 32,NONE)]
                   (stmt_seq
                      (stmt_ass lval_null
                         (e_call (funn_ext "register" "read")
                            [e_var (varn_name "counters");
                             e_var (varn_name "tmp");
                             e_var (varn_name "register_index")]))
                      (stmt_ass lval_null
                         (e_call (funn_ext "register" "write")
                            [e_var (varn_name "counters");
                             e_var (varn_name "register_index");
                             e_binop (e_var (varn_name "tmp")) binop_add
                               (e_v
                                  (v_bit
                                     ([F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; T],32)))]))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("register_index",d_none)]);
    ("esp_decrypt_aes_ctr",
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
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "ipsec_crypt" "decrypt_aes_ctr")
                   [e_var (varn_name "ipsecCrypt");
                    e_acc (e_var (varn_name "hdr")) "ipv4";
                    e_acc (e_var (varn_name "hdr")) "esp";
                    e_var (varn_name "standard_metadata");
                    e_var (varn_name "key"); e_var (varn_name "key_hmac")]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "header" "setInvalid")
                      [e_acc (e_var (varn_name "hdr")) "esp"]))
                (stmt_block [(varn_name "tmp",tau_bit 32,NONE)]
                   (stmt_seq
                      (stmt_ass lval_null
                         (e_call (funn_ext "register" "read")
                            [e_var (varn_name "counters");
                             e_var (varn_name "tmp");
                             e_var (varn_name "register_index")]))
                      (stmt_ass lval_null
                         (e_call (funn_ext "register" "write")
                            [e_var (varn_name "counters");
                             e_var (varn_name "register_index");
                             e_binop (e_var (varn_name "tmp")) binop_add
                               (e_v
                                  (v_bit
                                     ([F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; F; F; F; F; F; F; F; F;
                                       F; F; F; F; F; T],32)))]))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("key",d_none); ("key_hmac",d_none);
      ("register_index",d_none)]);
    ("l3_forward",
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
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "standard_metadata"))
                   "egress_spec") (e_var (varn_name "port")))
             (stmt_ass
                (lval_field
                   (lval_field (lval_varname (varn_name "hdr")) "ipv4") "ttl")
                (e_binop
                   (e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "ttl")
                   binop_sub (e_v (v_bit ([F; F; F; F; F; F; F; T],8))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("port",d_none)]);
    ("l2_forward",
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
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "standard_metadata"))
                   "egress_spec") (e_var (varn_name "port")))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_field (lval_varname (varn_name "hdr")) "ethernet")
                      "srcAddr")
                   (e_acc (e_acc (e_var (varn_name "hdr")) "ethernet")
                      "dstAddr"))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr"))
                            "ethernet") "dstAddr")
                      (e_var (varn_name "dstAddr")))
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr")) "ipv4")
                         "ttl")
                      (e_binop
                         (e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                            "ttl") binop_sub
                         (e_v (v_bit ([F; F; F; F; F; F; F; T],8))))))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("dstAddr",d_none); ("port",d_none)]);
    ("send_to_controller",
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
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "standard_metadata"))
                   "egress_spec")
                (e_v (v_bit ([F; F; F; F; T; F; F; F; F],9))))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "header" "setValid")
                      [e_acc (e_var (varn_name "hdr")) "cpu_header"]))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr"))
                            "cpu_header") "reason")
                      (e_var (varn_name "reason")))
                   (stmt_ass
                      (lval_field
                         (lval_field (lval_varname (varn_name "hdr"))
                            "cpu_header") "timestamp")
                      (e_acc (e_var (varn_name "standard_metadata"))
                         "ingress_global_timestamp")))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("reason",d_none)]);
    ("drop",
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
          (stmt_ass lval_null
             (e_call (funn_ext "" "mark_to_drop")
                [e_var (varn_name "standard_metadata")]))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)])],
   [(varn_name "current_register",tau_bit 32,NONE);
    (varn_name "do_drop",tau_bool,NONE);
    (varn_name "notify_hard",tau_bool,NONE);
    (varn_name "notify_soft",tau_bool,NONE);
    (varn_name "counters",tau_ext,NONE);
    (varn_name "ipsecCrypt",tau_ext,NONE)],[],
   [("spd",[mk_lpm; mk_exact],["add_spd_mark"; "drop"],"drop",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("forward",[mk_lpm],["l3_forward"; "l2_forward"; "drop"],"drop",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("sad_decrypt",[mk_exact; mk_exact; mk_exact],
     ["NoAction"; "esp_decrypt_aes_ctr"; "esp_decrypt_null"],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("sad_encrypt",[mk_lpm],
     ["esp_encrypt_aes_ctr"; "esp_encrypt_null"; "sadb_acquire"],
     "sadb_acquire",[e_v (v_bool T); e_v (v_bool F)])]);
  ("MyEgress",pbl_type_control,
   [("hdr",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
   [("MyEgress",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("MyComputeChecksum",pbl_type_control,[("hdr",d_inout); ("meta",d_inout)],
   [("MyComputeChecksum",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "" "update_checksum")
             [e_call (funn_ext "header" "isValid")
                [e_acc (e_var (varn_name "hdr")) "ipv4"];
              e_struct
                [("1",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "version");
                 ("2",e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "ihl");
                 ("3",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "diffserv");
                 ("4",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "totalLen");
                 ("5",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4")
                    "identification");
                 ("6",e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "flags");
                 ("7",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "fragOffset");
                 ("8",e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "ttl");
                 ("9",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "protocol");
                 ("10",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "srcAddr");
                 ("11",
                  e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "dstAddr")];
              e_acc (e_acc (e_var (varn_name "hdr")) "ipv4") "hdrChecksum";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; T; T; F],32))])),[])],[],
   [],[]);
  ("MyDeparser",pbl_type_control,[("packet",d_none); ("hdr",d_in)],
   [("MyDeparser",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "hdr")) "cpu_header"]))
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "packet_out" "emit")
                   [e_var (varn_name "packet");
                    e_acc (e_var (varn_name "hdr")) "ethernet"]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "packet_out" "emit")
                      [e_var (varn_name "packet");
                       e_acc (e_var (varn_name "hdr")) "ipv4"]))
                (stmt_ass lval_null
                   (e_call (funn_ext "packet_out" "emit")
                      [e_var (varn_name "packet");
                       e_acc (e_var (varn_name "hdr")) "esp"]))))),[])],[],
   [],[])],[("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f
   (v_struct
      [("cpu_header",
        v_header ARB
          [("zeros",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],64));
           ("reason",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16));
           ("port",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16));
           ("timestamp",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],
               48))]);
       ("ethernet",
        v_header ARB
          [("dstAddr",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],
               48));
           ("srcAddr",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],
               48));
           ("etherType",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16))]);
       ("ipv4",
        v_header ARB
          [("version",v_bit ([ARB; ARB; ARB; ARB],4));
           ("ihl",v_bit ([ARB; ARB; ARB; ARB],4));
           ("diffserv",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
           ("totalLen",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16));
           ("identification",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16));
           ("flags",v_bit ([ARB; ARB; ARB],3));
           ("fragOffset",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB],13));
           ("ttl",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
           ("protocol",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
           ("hdrChecksum",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16));
           ("srcAddr",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32));
           ("dstAddr",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32))]);
       ("esp",
        v_header ARB
          [("spi",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32));
           ("sequenceNumber",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32))])],
    v_struct
      [("intrinsic_metadata",
        v_struct
          [("ingress_global_timestamp",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],
               48))]);
       ("user_metadata",
        v_struct
          [("spd_mark",v_bit ([ARB; ARB; ARB; ARB],4));
           ("bypass",v_bool ARB)]);
       ("esp_meta",
        v_struct
          [("payloadLength",
            v_bit
              ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                ARB; ARB; ARB; ARB],16))])]),v1model_output_f,
 v1model_copyin_pbl,v1model_copyout_pbl,v1model_apply_table_f,
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

val basic_astate = ``((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
  [("spd",[]); ("forward",[]); ("sad_decrypt",[]); ("sad_encrypt",[])]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool ARB); ("miss",v_bool ARB);
       ("action_run",v_bit (REPLICATE 32 ARB,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate``;

(********************)
(* MANUAL ADDITIONS *)

(* TODO: Input has to be set up for every input packet type *)
val eth_input = mk_symb_packet_prefix "eth" 112;
val ipv4_input = mk_symb_packet_prefix "ip" 160;
val esp_input = mk_symb_packet_prefix "esp" 64;
val input = rhs $ concl $ EVAL “^eth_input ++ (^ipv4_input ++ ^esp_input)”;

val basic_astate_symb = rhs $ concl $ EVAL “p4_append_input_list [(^input,0)] ^basic_astate”;


(* RE-DEFINITIONS OF TROUBLESOME EXTERNS *)

Definition v1model_update_checksum':
 (v1model_update_checksum' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case assign scope_list (v_bit $ ((REPLICATE 16 (ARB:bool)), 16)) (lval_varname (varn_name "checksum")) of
   | SOME scope_list' =>
    SOME ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, scope_list', status_returnv v_bot)
   | NONE => NONE
 )
End

val pre_ctx = basic_actx;

Definition ctx'_def:
  ctx' = ^(replace_ext_impl pre_ctx "" "update_checksum" “v1model_update_checksum'”)
End

val ctx = rhs $ concl $ EVAL ``ctx'``;
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "basic_ctx" (mk_eq(mk_var("basic_ctx", type_of ctx), ctx));

(* OLD
val ctx = basic_actx;
val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn "basic_ctx" (mk_eq(mk_var("basic_ctx", type_of ctx), ctx));
*)

fun is_finished' i_end step_thm =
 let
  val astate = p4_testLib.the_final_state_imp step_thm
  val (aenv, _, _, _) = p4Syntax.dest_astate astate
  val (i, io_list, _, _) = p4Syntax.dest_aenv aenv
 in
  (* Whenever the result of taking one step is at block index i, we're finished *)
  if numSyntax.int_of_term i = i_end andalso null $ fst $ listSyntax.dest_list io_list
  then true
  else false
 end
;

(* These are defined to enable easier debugging *)
val (fty_map, b_fty_map) = (basic_ftymap, basic_blftymap);
val const_actions_tables = [];
val arch_ty = p4_v1modelLib.v1model_arch_ty
val init_astate = basic_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val path_cond = (ASSUME T)
val n_max = 300;
val debug_flag = true;
val p4_is_finished_alt_opt = (SOME (is_finished' 5));
val postcond = “(\s. T):v1model_ascope astate -> bool”;

(* TODO: Free variables in register extern objects *)

val time_start = Time.now();
(*
val p4_symb_exec_fun = (p4_symb_exec 1)
*)
val contract_thm = p4_symb_exec_prove_contract_conc debug_flag arch_ty ctx (basic_ftymap, basic_blftymap) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond p4_is_finished_alt_opt n_max postcond;
val _ = print (String.concat ["Total time consumption: ",
                              (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
                              " ms\n"]);

val _ = export_theory ();
