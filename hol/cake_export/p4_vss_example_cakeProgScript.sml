open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_vss_example_cakeProg";

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;
open p4_coreTheory p4_vssTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_vss_cakeProgTheory;

val _ = intLib.deprecate_int();
val _ = (max_print_depth := 1000);

val _ = translation_extends "p4_exec_sem_vss_cakeProg";

(***************)
(* VSS example *)

val vss_actx =
   “([arch_block_inp;
      arch_block_pbl "parser"
        [e_var (varn_name "b"); e_var (varn_name "parsedHeaders")];
      arch_block_ffbl "parser_runtime";
      arch_block_pbl "pipe"
        [e_var (varn_name "headers"); e_var (varn_name "parseError");
         e_var (varn_name "inCtrl"); e_var (varn_name "outCtrl")];
      arch_block_ffbl "pre_deparser";
      arch_block_pbl "deparser"
        [e_var (varn_name "outputHeaders"); e_var (varn_name "b")];
      arch_block_out],
     [("parser",pbl_type_parser,[("b",d_none); ("p",d_out)],
       [("parser",
         stmt_seq
           (stmt_ass lval_null
              (e_call (funn_inst "Checksum16") [e_var (varn_name "ck")]))
           (stmt_trans (e_v (v_str "start"))),[])],
       [(varn_name "ck",tau_ext,NONE)],
       [("start",
         stmt_block []
           (stmt_seq
              (stmt_ass lval_null
                 (e_call (funn_ext "packet_in" "extract")
                    [e_var (varn_name "b");
                     e_acc (e_var (varn_name "p")) "ethernet"]))
              (stmt_trans
                 (e_select
                    (e_struct
                       [("",
                         e_acc (e_acc (e_var (varn_name "p")) "ethernet")
                           "etherType")])
                    [([s_sing (v_bit (fixwidth 16 $ n2v 2048,16))],"parse_ipv4")] "reject"))));
        ("parse_ipv4",
         stmt_block []
           (stmt_seq
              (stmt_ass lval_null
                 (e_call (funn_ext "packet_in" "extract")
                    [e_var (varn_name "b");
                     e_acc (e_var (varn_name "p")) "ip"]))
              (stmt_seq
                 (stmt_ass lval_null
                    (e_call (funn_ext "" "verify")
                       [e_binop
                          (e_acc (e_acc (e_var (varn_name "p")) "ip")
                             "version") binop_eq (e_v (v_bit (fixwidth 4 $ n2v 4,4)));
                        e_v (v_bit (fixwidth 32 $ n2v 8,32))]))
                 (stmt_seq
                    (stmt_ass lval_null
                       (e_call (funn_ext "" "verify")
                          [e_binop
                             (e_acc (e_acc (e_var (varn_name "p")) "ip")
                                "ihl") binop_eq (e_v (v_bit (fixwidth 4 $ n2v 5,4)));
                           e_v (v_bit (fixwidth 32 $ n2v 7,32))]))
                    (stmt_seq
                       (stmt_ass lval_null
                          (e_call (funn_ext "Checksum16" "clear")
                             [e_var (varn_name "ck")]))
                       (stmt_seq
                          (stmt_ass lval_null
                             (e_call (funn_ext "Checksum16" "update")
                                [e_var (varn_name "ck");
                                 e_acc (e_var (varn_name "p")) "ip"]))
                          (stmt_seq
                             (stmt_ass lval_null
                                (e_call (funn_ext "" "verify")
                                   [e_binop
                                      (e_call (funn_ext "Checksum16" "get")
                                         [e_var (varn_name "ck")]) binop_eq
                                      (e_v (v_bit (fixwidth 16 $ n2v 0,16)));
                                    e_v (v_bit (fixwidth 32 $ n2v 9,32))]))
                             (stmt_trans (e_v (v_str "accept"))))))))))],[]);
      ("pipe",pbl_type_control,
       [("headers",d_inout); ("parseError",d_in); ("inCtrl",d_in);
        ("outCtrl",d_out)],
       [("pipe",
         stmt_block []
           (stmt_seq
              (stmt_cond
                 (e_binop (e_var (varn_name "parseError")) binop_neq
                    (e_v (v_bit (fixwidth 32 $ n2v 0,32))))
                 (stmt_seq
                    (stmt_ass lval_null (e_call (funn_name "Drop_action") []))
                    (stmt_ret (e_v v_bot))) stmt_empty)
              (stmt_seq
                 (stmt_seq
                    (stmt_app "ipv4_match"
                       [e_acc (e_acc (e_var (varn_name "headers")) "ip")
                          "dstAddr"])
                    (stmt_cond
                       (e_binop
                          (e_acc (e_var (varn_name "outCtrl")) "outputPort")
                          binop_eq (e_var (varn_name "DROP_PORT")))
                       (stmt_ret (e_v v_bot)) stmt_empty))
                 (stmt_seq
                    (stmt_seq
                       (stmt_app "check_ttl"
                          [e_acc (e_acc (e_var (varn_name "headers")) "ip")
                             "ttl"])
                       (stmt_cond
                          (e_binop
                             (e_acc (e_var (varn_name "outCtrl"))
                                "outputPort") binop_eq
                             (e_var (varn_name "CPU_OUT_PORT")))
                          (stmt_ret (e_v v_bot)) stmt_empty))
                    (stmt_seq
                       (stmt_seq
                          (stmt_app "dmac" [e_var (varn_name "nextHop")])
                          (stmt_cond
                             (e_binop
                                (e_acc (e_var (varn_name "outCtrl"))
                                   "outputPort") binop_eq
                                (e_var (varn_name "CPU_OUT_PORT")))
                             (stmt_ret (e_v v_bot)) stmt_empty))
                       (stmt_app "smac"
                          [e_acc (e_var (varn_name "outCtrl")) "outputPort"]))))),
         []);
        ("Drop_action",
         stmt_seq
           (stmt_ass
              (lval_field (lval_varname (varn_name "outCtrl")) "outputPort")
              (e_var (varn_name "DROP_PORT"))) (stmt_ret (e_v v_bot)),[]);
        ("Set_nhop",
         stmt_seq
           (stmt_ass (lval_varname (varn_name "nextHop"))
              (e_var (varn_name "ipv4_dest")))
           (stmt_seq
              (stmt_ass
                 (lval_field
                    (lval_field (lval_varname (varn_name "headers")) "ip")
                    "ttl")
                 (e_binop
                    (e_acc (e_acc (e_var (varn_name "headers")) "ip") "ttl")
                    binop_sub (e_v (v_bit (fixwidth 8 $ n2v 1,8)))))
              (stmt_seq
                 (stmt_ass
                    (lval_field (lval_varname (varn_name "outCtrl"))
                       "outputPort") (e_var (varn_name "port")))
                 (stmt_ret (e_v v_bot)))),
         [("ipv4_dest",d_none); ("port",d_none)]);
        ("Send_to_cpu",
         stmt_seq
           (stmt_ass
              (lval_field (lval_varname (varn_name "outCtrl")) "outputPort")
              (e_var (varn_name "CPU_OUT_PORT"))) (stmt_ret (e_v v_bot)),[]);
        ("Set_dmac",
         stmt_seq
           (stmt_ass
              (lval_field
                 (lval_field (lval_varname (varn_name "headers")) "ethernet")
                 "dstAddr") (e_var (varn_name "dmac")))
           (stmt_ret (e_v v_bot)),[("dmac",d_none)]);
        ("Set_smac",
         stmt_seq
           (stmt_ass
              (lval_field
                 (lval_field (lval_varname (varn_name "headers")) "ethernet")
                 "srcAddr") (e_var (varn_name "smac")))
           (stmt_ret (e_v v_bot)),[("smac",d_none)])],
       [(varn_name "nextHop",tau_bit 32,NONE)],[],
       [("ipv4_match",[mk_lpm],"Drop_action",[]);
        ("check_ttl",[mk_exact],"NoAction",[]);
        ("dmac",[mk_exact],"Drop_action",[]);
        ("smac",[mk_exact],"Drop_action",[])]);
      ("deparser",pbl_type_control,[("p",d_inout); ("b",d_none)],
       [("deparser",
         stmt_block []
           (stmt_seq
              (stmt_ass lval_null
                 (e_call (funn_inst "Checksum16") [e_var (varn_name "ck")]))
              (stmt_seq
                 (stmt_ass lval_null
                    (e_call (funn_ext "packet_out" "emit")
                       [e_var (varn_name "b");
                        e_acc (e_var (varn_name "p")) "ethernet"]))
                 (stmt_seq
                    (stmt_cond
                       (e_call (funn_ext "header" "isValid")
                          [e_acc (e_var (varn_name "p")) "ip"])
                       (stmt_seq
                          (stmt_ass lval_null
                             (e_call (funn_ext "Checksum16" "clear")
                                [e_var (varn_name "ck")]))
                          (stmt_seq
                             (stmt_ass
                                (lval_field
                                   (lval_field (lval_varname (varn_name "p"))
                                      "ip") "hdrChecksum")
                                (e_v (v_bit (fixwidth 16 $ n2v 0,16))))
                             (stmt_seq
                                (stmt_ass lval_null
                                   (e_call (funn_ext "Checksum16" "update")
                                      [e_var (varn_name "ck");
                                       e_acc (e_var (varn_name "p")) "ip"]))
                                (stmt_ass
                                   (lval_field
                                      (lval_field
                                         (lval_varname (varn_name "p")) "ip")
                                      "hdrChecksum")
                                   (e_call (funn_ext "Checksum16" "get")
                                      [e_var (varn_name "ck")])))))
                       stmt_empty)
                    (stmt_ass lval_null
                       (e_call (funn_ext "packet_out" "emit")
                          [e_var (varn_name "b");
                           e_acc (e_var (varn_name "p")) "ip"]))))),[])],
       [(varn_name "ck",tau_ext,NONE)],[],[])],
     [("parser_runtime",ffblock_ff vss_parser_runtime);
      ("pre_deparser",ffblock_ff vss_pre_deparser)],
     vss_input_f
       (v_struct
          [("ethernet",
            v_header F
              [("dstAddr",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F],48));
               ("srcAddr",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F],48));
               ("etherType",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F],16))]);
           ("ip",
            v_header F
              [("version",v_bit ([F; F; F; F],4));
               ("ihl",v_bit ([F; F; F; F],4));
               ("diffserv",v_bit ([F; F; F; F; F; F; F; F],8));
               ("totalLen",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F],16));
               ("identification",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F],16));
               ("flags",v_bit ([F; F; F],3));
               ("fragOffset",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F],13));
               ("ttl",v_bit ([F; F; F; F; F; F; F; F],8));
               ("protocol",v_bit ([F; F; F; F; F; F; F; F],8));
               ("hdrChecksum",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F],16));
               ("srcAddr",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F],32));
               ("dstAddr",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F],32))])]),
     vss_output_f,vss_copyin_pbl',vss_copyout_pbl',vss_apply_table_f,
     [("header",NONE,
       [("isValid",[("this",d_in)],header_is_valid);
        ("setValid",[("this",d_inout)],header_set_valid);
        ("setInvalid",[("this",d_inout)],header_set_invalid)])] ⧺
     [("",NONE,[("verify",[("condition",d_in); ("err",d_in)],vss_verify)]);
      ("packet_in",NONE,
       [("extract",[("this",d_in); ("headerLvalue",d_out)],
         vss_packet_in_extract)(* ;
        ("lookahead",[("this",d_in); ("dummy_T",d_in)],
         vss_packet_in_lookahead);
        ("advance",[("this",d_in); ("bits",d_in)],vss_packet_in_advance) *)]);
      ("packet_out",NONE,
       [("emit",[("this",d_in); ("data",d_in)],vss_packet_out_emit)]);
      ("Checksum16",SOME ([("this",d_out)],Checksum16_construct),
       [("clear",[("this",d_in)],Checksum16_clear);
        ("update",[("this",d_in); ("data",d_in)],Checksum16_update);
        ("get",[("this",d_in)],Checksum16_get)])],
     [("NoAction",stmt_ret (e_v v_bot),[])]):vss_ascope actx”

(* TODO: Apart from the table and extern configurations, this seems close to a generic P4 initial state *)
val vss_astate = “((0,
       [],[],0,[],[("parseError",v_bit (REPLICATE 32 F,32))],
       [("ipv4_match",
         [(($= [e_v (v_bit (REPLICATE 32 F,32))],0),"Set_nhop",
           [e_v (v_bit (fixwidth 32 $ n2v 1,32)); e_v (v_bit (REPLICATE 4 F,4))])]);
        ("dmac",
         [(($= [e_v (v_bit (fixwidth 32 $ n2v 1,32))],0),"Set_dmac",
           [e_v (v_bit (fixwidth 48 $ n2v 1,48))])]);
        ("smac",
         [(($= [e_v (v_bit (REPLICATE 4 F,4))],0),"Set_smac",
           [e_v (v_bit (REPLICATE 48 F,48))])])]),
      [[(varn_name "REAL_PORT_COUNT",v_bit (fixwidth 4 $ n2v 8,4),NONE);
        (varn_name "RECIRCULATE_IN_PORT",v_bit (fixwidth 4 $ n2v 13,4),NONE);
        (varn_name "CPU_IN_PORT",v_bit (fixwidth 4 $ n2v 14,4),NONE);
        (varn_name "DROP_PORT",v_bit (fixwidth 4 $ n2v 15,4),NONE);
        (varn_name "CPU_OUT_PORT",v_bit (fixwidth 4 $ n2v 14,4),NONE);
        (varn_name "RECIRCULATE_OUT_PORT",v_bit (fixwidth 4 $ n2v 13,4),NONE);
        (varn_name "gen_apply_result",
         v_struct
           [("hit",v_bool F); ("miss",v_bool F);
            ("action_run",v_bit (REPLICATE 32 F,32))],NONE)]],
      arch_frame_list_empty,status_running):vss_ascope astate”;

val n_max = “205:num”;

(*

fun deparse_bool_list l =
   case l of
     [] => []
   | h::t =>
    if Teq h
    then (#"1"::(deparse_bool_list t))
    else (#"0"::(deparse_bool_list t))
 ;

(* Code from VSS example, generating input *)
val input_port_ok = ``1:num``;
val input_data_ok = listSyntax.mk_list ([], bool);
val input_ttl_ok = 1;
val input_ipv4_ok = p4_testLib.mk_ipv4_packet_ok input_data_ok input_ttl_ok;
val input_ok = p4_testLib.mk_eth_frame_ok input_ipv4_ok;

(* From VSS TTL example, with symbolic bits made concrete with zeroed values *)
val input = “([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; T; F; T;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F;
     T; F; T; T; T; F; F; T; T; T; T; F; T; F; T; T; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],1:num)”;
val bl_input_tm = fst $ dest_pair input

(* Entire state after a number of steps *)

EVAL “arch_multi_exec ^vss_actx (p4_append_input_list [^input] ^vss_astate) 181”

  val cake_top_exec_def =
   Define
    ‘cake_top_exec input =
      case
       arch_multi_exec' ^vss_actx
	(p4_append_input_list [input] ^vss_astate) ^n_max of
      | SOME res => SOME $ p4_get_output_list res
      | NONE => NONE’;

EVAL “cake_top_exec ^input”
EVAL “arch_multi_exec' ^vss_actx (p4_append_input_list [^input] ^vss_astate) ^n_max”

val bl_input = String.implode $ deparse_bool_list $ fst $ listSyntax.dest_list bl_input_tm

*)

p4_cake_wrapperLib.translate_p4 "vss_example" vss_actx vss_astate n_max;

  
val _ = export_theory ();
