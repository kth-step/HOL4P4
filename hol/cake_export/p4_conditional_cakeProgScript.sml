open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_conditional_cakeProg";

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;
open p4_coreTheory p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_v1model_cakeProgTheory;

open fromSexpTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 1000);

val _ = translation_extends "p4_exec_sem_v1model_cakeProg";

(***********************)
(* Conditional example *)

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
     [])],[],[],[])],[("postparser",ffblock_ff v1model_postparser')],
 v1model_input_f'
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
    v_struct []),v1model_output_f,v1model_copyin_pbl',v1model_copyout_pbl',
 v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify);
(*
    ("verify_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_in); ("algo",d_none)],
     v1model_verify_checksum);

    ("update_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_inout);
      ("algo",d_none)],v1model_update_checksum) *) ]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract')]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]) (* ;
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)])
*)
],
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

(* TODO: Apart from the table and extern configurations, this seems close to a generic P4 initial state *)
val symb_exec1_astate = “((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],[]),
    [[(varn_name "gen_apply_result",
       v_struct
         [("hit",v_bool F); ("miss",v_bool F);
          ("action_run",v_bit (REPLICATE 32 F,32))],NONE)]],
    arch_frame_list_empty,status_running):v1model_ascope astate”;

(* 44 seems to work also with arch_multi_exec, 45 doesn't work *)
val n_max = “45:num”;


(*************************)
(* Generic wrapper parts *)

Definition symb_exec1_exec_def:
 symb_exec1_exec input =
  case
   arch_multi_exec' ^symb_exec1_actx
    (p4_append_input_list [input] ^symb_exec1_astate) ^n_max of
  | SOME res => SOME $ p4_get_output_list res
  | NONE => NONE
End

val _ = translate p4_append_input_list_def;
val _ = translate p4_get_output_list_def;
val _ = translate symb_exec1_exec_def;

(*

exception ParseError of string;

fun parse_bool_list l =
   case l of
     [] => []
   | h::t =>
    if h = #"0"
    then (F::(parse_bool_list t))
    else if h = #"1"
    then (T::(parse_bool_list t))
    else raise ParseError ("Error: packet (first command-line argument) should be specified using only 0s and 1s to signify bits.\n");

fun deparse_bool_list l =
   case l of
     [] => []
   | h::t =>
    if Teq h
    then (#"1"::(deparse_bool_list t))
    else (#"0"::(deparse_bool_list t))
 ;

val input = listSyntax.mk_list (parse_bool_list $ String.explode "010010101001001011111111100100101", bool)


val input = “([F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
               F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0:num)”;
val bl_input_tm = fst $ dest_pair input




EVAL “symb_exec1_exec ^input”

val bl_input = String.implode $ deparse_bool_list $ fst $ listSyntax.dest_list bl_input_tm

Definition symb_exec1_exec_old_def:
 symb_exec1_exec_old input =
  case
   arch_multi_exec ^symb_exec1_actx
    (p4_append_input_list [input] ^symb_exec1_astate) ^n_max of
  | SOME res => SOME $ p4_get_output_list res
  | NONE => NONE
End

EVAL “symb_exec1_exec_old ^input”

*)


(* TODO: Change this to Quote cakeml: syntax? *)
val _ = append_prog o process_topdecs $ 
 ‘exception ParseError string;’
;

val _ = append_prog o process_topdecs $ 
 ‘fun parse_bool_list l =
   case l of
     [] => []
   | h::t =>
    if h = #"0"
    then (False::(parse_bool_list t))
    else if h = #"1"
    then (True::(parse_bool_list t))
    else raise ParseError ("Error: packet (first command-line argument) should be specified using only 0s and 1s to signify bits.\n")
 ;
’;

val _ = append_prog o process_topdecs $ 
 ‘fun deparse_bool_list l =
   case l of
     [] => []
   | h::t =>
    if h
    then (#"T"::(deparse_bool_list t))
    else (#"F"::(deparse_bool_list t))
 ;’;

val _ = append_prog o process_topdecs $ 
 ‘fun print_output_packets l =
   case l of
     [] => ()
   | (out_bl, out_port)::t =>
    let
     val out_packet_string = String.implode (deparse_bool_list out_bl)
    in
     print(out_packet_string ^ " at port "); print_int out_port; print "\n"; print_output_packets t
    end
 ;’;

val _ = append_prog o process_topdecs $ 
 ‘fun main () =
   let
     val packet_arg::rest = (CommandLine.arguments())
     val port_arg = List.hd rest

     val bl = parse_bool_list (String.explode packet_arg)
     val in_port = Option.valOf (Int.fromString port_arg)
     val in_packet_string = String.implode (deparse_bool_list bl)
   in
    (case symb_exec1_exec (bl, in_port) of
       None => raise ParseError ("Error: execution result is None.\n")
     | Some output_packets =>
       (print ("Input packet was: " ^ in_packet_string ^ " at port "); print_int in_port; print "\n";
       print "Output packet(s) are: "; print_output_packets output_packets))
   end
   handle ParseError parse_err_msg => TextIO.print_err parse_err_msg
   handle _ =>
     TextIO.print_err ("Usage: " ^ CommandLine.name() ^ " <n>\n");’;

(* TODO: Can this be replaced with something more short-handish? *)
val prog =
 “SNOC
   (Dlet unknown_loc (Pcon NONE [])
    (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)”
  |> EVAL |> concl |> rhs;

val _ = astToSexprLib.write_ast_to_file "conditional_test.sexp" prog;
    
val _ = export_theory ();
