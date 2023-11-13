open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

open p4_symb_execLib;

val _ = new_theory "p4_symb_exec_test1";


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
 [("p",
   pblock_regular pbl_type_parser
     [("p",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
       [("b",d_none); ("h",d_out); ("m",d_inout); ("sm",d_inout)])] []
     [("start",
       stmt_seq
         (stmt_ass lval_null
            (e_call (funn_ext "packet_in" "extract")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"]))
         (stmt_trans (e_v (v_str "accept"))))] []);
  ("vrfy",
   pblock_regular pbl_type_control
     [("vrfy",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("update",
   pblock_regular pbl_type_control
     [("update",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("egress",
   pblock_regular pbl_type_control
     [("egress",stmt_seq stmt_empty stmt_empty,
       [("h",d_inout); ("m",d_inout); ("sm",d_inout)])] [] [] []);
  ("deparser",
   pblock_regular pbl_type_control
     [("deparser",
       stmt_seq stmt_empty
         (stmt_ass lval_null
            (e_call (funn_ext "packet_out" "emit")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"])),
       [("b",d_none); ("h",d_in)])] [] [] []);
  ("ingress",
   pblock_regular pbl_type_control
     [("ingress",
       stmt_seq stmt_empty
         (stmt_cond
            (e_binop
               (e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e")
               binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))))),
       [("h",d_inout); ("m",d_inout); ("standard_meta",d_inout)])] [] [] [])],
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
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify)]);
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
 [("NoAction",stmt_seq stmt_empty (stmt_ret (e_v v_bot)),[])]):v1model_ascope actx``;

val symb_exec1_astate = rhs $ concl $ EVAL “(p4_append_input_list [([F; F; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; T; F; F; F; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; F; T; T; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; T; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;


(*
(* eval_under_assum: *)
GEN_ALL $ eval_under_assum p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate [] [] (ASSUME T) 10;
*)

val symb_exec1_astate_symb = rhs $ concl $ EVAL “(p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;



(* symb_exec: *)
(* Parameter assignment for debugging: *)
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec1_actx
val init_astate = symb_exec1_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val path_cond = (ASSUME T)
val fuel = 2
(*
val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl
*)

(* Before branch
val [(path_cond, step_thm)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 24
*)

(* Branch happens here *)
val [(path_cond, step_thm), (path_cond2, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 25

(*
val [(path_cond, step_thm), (path_cond2, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 26

val [(path_cond, step_thm), (path_cond2, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 28
*)

val _ = export_theory ();