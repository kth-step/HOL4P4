open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_cake_test2";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib;

intLib.deprecate_int();
val _ = (max_print_depth := 1000);

open p4_exec_sem_cakeProgTheory;
open p4_cake_transformLib p4_cake_auxLib;

val _ = translation_extends "p4_exec_sem_cakeProg";

(* This file contains a test export of a program (switches port between 1 and 2) that has
 * been rewritten to a CakeML-friendly representation, where variable names have been
 * replaced with words. *)

val actx = ``([arch_block_inp;
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
             (e_acc (e_var (varn_name "standard_meta")) "ingress_port")
             binop_eq (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))))
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_meta"))
                "egress_spec") (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))),
     [])],[],[],[])],[("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f
   (v_struct
      [("h",
        v_header F
          [("row",
            v_struct
              [("e",v_bit ([F; F; F; F; F; F; F; F],8));
               ("t",
                v_bit
                  ([F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F],16));
               ("l",v_bit ([F; F; F; F; F; F; F; F],8));
               ("r",v_bit ([F; F; F; F; F; F; F; F],8));
               ("v",v_bit ([F; F; F; F; F; F; F; F],8))])])],
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

val astate = “((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],[]),
    [[(varn_name "gen_apply_result",
       v_struct
         [("hit",v_bool F); ("miss",v_bool F);
          ("action_run",v_bit (REPLICATE 32 F,32))],NONE)]],
    arch_frame_list_empty,status_running):v1model_ascope astate”;

(* Test input and output:

UDP:

dest_some $ rhs $ concl $ EVAL “fromHexString "52540012345602426f2d812208004500002d0001400040117c410a0000010a00000230393039001900005445535420554450204d455353414745"”

          EVAL “num_to_bin_string ^it”

val in_str = "1010010010101000000000000010010001101000101011000000010010000100110111100101101100000010010001000001000000000000100010100000000000000000010110100000000000000010100000000000000010000000001000101111100010000010000101000000000000000000000000100001010000000000000000000000010001100000011100100110000001110010000000000011001000000000000000001010100010001010101001101010100001000000101010101000100010100000010000001001101010001010101001101010011010000010100011101000101"

val input = parse_bool_list in_str;

val input = mk_pair (input, “1:num”)
    

(* TODO: Where did the old input ("010010101001001011111111100100101") come from? *)
val input = parse_bool_list "111111111111111111111111111111111111111111111111110010101100000000111011000100111100001010110011000010000000011000000000000000010000100000000000000001100000010000000000000000011100101011000000001110110001001111000010101100110000101000000000000000000000000100000000000000000000000000000000000000000000000000001010000000000000000000000010"
   
val input = “([T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
     T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
     T; T; F; F; T; F; T; F; T; T; F; F; F; F; F; F; F; F; T; T; T; F; T; T;
     F; F; F; T; F; F; T; T; T; T; F; F; F; F; T; F; T; F; T; T; F; F; T; T;
     F; F; F; F; T; F; F; F; F; F; F; F; F; T; T; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; T; T; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; T; T; T; F; F; T; F; T; F; T; T; F; F; F; F; F; F;
     F; F; T; T; T; F; T; T; F; F; F; T; F; F; T; T; T; T; F; F; F; F; T; F;
     T; F; T; T; F; F; T; T; F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F],1:num)”;
val bl_input_tm = fst $ dest_pair input

val bl_input = deparse_bool_list bl_input_tm

*)


(** Transformation **)

val (dict', actx', astate') =
 transform_program v1model_dict actx astate

(*

val res = dest_some $ rhs $ concl $ EVAL “arch_multi_exec' ^actx' (p4_append_input_list' [^input] ^astate') 200”


UDP output:

val out_bin = deparse_bool_list “[T; F; T; F; F; T; F; F; T; F; T; F; T; F; F; F; F; F; F; F; F; F;
 F; F; F; F; T; F; F; T; F; F; F; T; T; F; T; F; F; F; T; F; T; F;
 T; T; F; F; F; F; F; F; F; T; F; F; T; F; F; F; F; T; F; F; T; T;
 F; T; T; T; T; F; F; T; F; T; T; F; T; T; F; F; F; F; F; F; T; F;
 F; T; F; F; F; T; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F;
 F; F; T; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
 F; F; F; F; F; T; F; T; T; F; T; F; F; F; F; F; F; F; F; F; F; F;
 F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
 T; F; F; F; F; F; F; F; F; F; T; F; F; F; T; F; T; T; T; T; T; F;
 F; F; T; F; F; F; F; F; T; F; F; F; F; T; F; T; F; F; F; F; F; F;
 F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F;
 F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
 F; F; F; F; F; T; F; F; F; T; T; F; F; F; F; F; F; T; T; T; F; F;
 T; F; F; T; T; F; F; F; F; F; F; T; T; T; F; F; T; F; F; F; F; F;
 F; F; F; F; F; F; T; T; F; F; T; F; F; F; F; F; F; F; F; F; F; F;
 F; F; F; F; F; F; T; F; T; F; T; F; F; F; T; F; F; F; T; F; T; F;
 T; F; T; F; F; T; T; F; T; F; T; F; T; F; F; F; F; T; F; F; F; F;
 F; F; T; F; T; F; T; F; T; F; T; F; F; F; T; F; F; F; T; F; T; F;
 F; F; F; F; F; T; F; F; F; F; F; F; T; F; F; T; T; F; T; F; T; F;
 F; F; T; F; T; F; T; F; T; F; F; T; T; F; T; F; T; F; F; T; T; F;
 T; F; F; F; F; F; T; F; T; F; F; F; T; T; T; F; T; F; F; F; T; F;
 T]”

rhs $ concl $ EVAL “num_to_hex_string $ THE $ fromBinString ^(stringLib.fromMLstring out_bin)”
        
*)

val dict'' = invert_dict dict'

(** CakeML export **)

val progname = "ffi_test";
val dict = dict'';
val actx = actx';
val astate = astate';
val n_max = “1000:num”;
val debug_mode = false;

p4_cake_wrapper_ffiLib.translate_p4 progname dict actx astate n_max debug_mode;

val _ = export_theory ();
