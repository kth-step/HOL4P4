structure p4_cake_wrapperLib :> p4_cake_wrapperLib = struct

open HolKernel boolLib Parse bossLib;

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;
open p4_coreTheory p4_vssTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;
open fromSexpTheory;

val _ = intLib.deprecate_int();

(* Note that this function only adds inlined CakeML code - it translates no HOL4
 * definitions.
 * The function provides a command-line interface that passes an incoming packet in a
 * format of ones and zeroes (e.g. "1010010001010101") and an ingress port in the format
 * of a number (e.g. "42"). This is then used as input to the top-level execution function
 * cake_top_exec. *)
fun append_prog_p4_wrapper () =
 let
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
       (case cake_top_exec (bl, in_port) of
	  None => raise ParseError ("Error: execution result is None.\n")
	| Some output_packets =>
	  (print ("Input packet was: " ^ in_packet_string ^ " at port "); print_int in_port; print "\n";
	  print "Output packet(s) are: "; print_output_packets output_packets))
      end
      handle ParseError parse_err_msg => TextIO.print_err parse_err_msg
      handle _ =>
	TextIO.print_err ("Usage: " ^ CommandLine.name() ^ " <n>\n");’;
 in
  (* TODO: Can this be replaced with something more short-handish? *)
  “SNOC
    (Dlet unknown_loc (Pcon NONE [])
     (App Opapp [Var (Short "main"); Con NONE []]))
     ^(get_ml_prog_state() |> get_prog)”
   |> EVAL |> concl |> rhs
 end
;

(* This function takes a program name as a string (e.g. "test_program", without suffix),
 * an actx and astate (HOL4 terms which can be obtained from the HOL4P4 import tool)
 * a maximum number of reduction steps (e.g. 140) and then constructs a CakeML sexp that
 * can be compiled to a command-line program that concretely executes the P4 program in
 * actx from the initial state astate, then prints the resulting outgoing packets. *)
fun translate_p4 progname actx astate n_max =
 let
  val cake_top_exec_def =
   Define
    ‘cake_top_exec input =
      case
       arch_multi_exec' ^actx
	(p4_append_input_list [input] ^astate) ^n_max of
      | SOME res => SOME $ p4_get_output_list res
      | NONE => NONE’;

  (* TODO: This is the bottleneck... *)
  val _ = translate cake_top_exec_def;

  val prog = append_prog_p4_wrapper ();
 in
  astToSexprLib.write_ast_to_file (progname^".sexp") prog
 end
;

end
