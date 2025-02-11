structure p4_cake_wrapperLib :> p4_cake_wrapperLib = struct

open HolKernel boolLib Parse bossLib;

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory p4_vssTheory;
open p4_exec_sem_cakeTheory;
open p4_arch_cakeTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisFunctionsLib;
open fromSexpTheory;

open stringTheory;

val _ = intLib.deprecate_int();

(* Note that this function only adds inlined CakeML code - it translates no HOL4
 * definitions.
 * The function provides a command-line interface that passes an incoming packet in a
 * format of ones and zeroes (e.g. "1010010001010101") and an ingress port in the format
 * of a number (e.g. "42"). This is then used as input to the top-level execution function
 * cake_top_exec. *)
(* TODO: Add common debug functions to a new ProgScript file *)
fun append_prog_p4_wrapper debug_mode () =
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
	print "Output packet(s) are: "; print(out_packet_string); print(" at port "); print_int out_port; print "\n"; print_output_packets t
       end
    ;’;

   val _ =
    if debug_mode
    then
     let

      val _ = append_prog o process_topdecs $
       ‘fun get_scope_list ((aenv, (g_scope_list', (arch_frame_list', status'))):v1model_ascope' astate') =
	 case get_frame_list arch_frame_list' of
           None =>
          let
           val _ = print "Can't get current scope list: arch_frame_list is empty.\n"
          in 
           None
          end
         | Some frame_list =>
          (case frame_list of
             ((funn, (stmt_stack, scope_list))::t) => Some scope_list
           | [] =>
	    let
	     val _ = print "Can't get current scope list: frame_list is [].\n"
	    in 
	     None
	    end);’;

      val _ = append_prog o process_topdecs $
       ‘fun get_block_index ((i, (io_list, (io_list', ascope))):v1model_ascope' aenv') = i;’;

      val _ = append_prog o process_topdecs $
       ‘fun print_frame_name frame_list =
         (print "in function ";
	  print (case frame_list of
	     ((funn, (stmt_stack, scope_list))::t) =>
	    (case get_funn_string funn of
	      None => String.implode (unknown_function 1)
	     | Some name => String.implode name)
	   | [] => String.implode (empty_frame_list 1)));’;

      val _ = append_prog o process_topdecs $
       ‘fun arch_multi_exec'_debug (actx:v1model_ascope' actx') ((aenv, (g_scope_list', (arch_frame_list', status'))):v1model_ascope' astate') (fuel:int) =
	 (case fuel of
	    0 => Some ((aenv, (g_scope_list', (arch_frame_list', status'))):v1model_ascope' astate')
	  | n =>
	   (case arch_exec' actx ((aenv, (g_scope_list', (arch_frame_list', status')))) of
	      Some astate' =>
             let
              val _ = (print ("At fuel "); print_int fuel; print ": State before exec: ")
              val _ = (print "block index "; print_int (get_block_index aenv); print ", ")
              val _ =
               (case get_frame_list arch_frame_list' of
                     None => print "empty frame list.\n"
                   | Some frame_list => (print "regular frame list, "; print_frame_name frame_list; print ".\n"))

             in
	      arch_multi_exec'_debug actx astate' (n-1)
             end
	    | None =>
             Some ((aenv, (g_scope_list', (arch_frame_list', status'))))));’;

      val _ = append_prog o process_topdecs $
      ‘fun cake_top_exec_debug (input:((bool list) * int)) = 
	 (case
	  arch_multi_exec'_debug (actx_debug 1)
	   (p4_append_input_list'_debug [input] (astate_debug 1)) (n_max_debug 1) of
	   Some res => Some (p4_get_output_list_debug res)
	  | None => None);’;

      val _ = append_prog o process_topdecs $
      ‘fun main () =
       let
	 val packet_arg::rest = (CommandLine.arguments())
	 val port_arg = List.hd rest

	 val bl = parse_bool_list (String.explode packet_arg)
	 val in_port = Option.valOf (Int.fromString port_arg)
	 val in_packet_string = String.implode (deparse_bool_list bl)
       in
	(case cake_top_exec_debug (bl, in_port) of
	   None => raise ParseError ("Error: execution result is None.\n")
	 | Some output_packets =>
	   (print ("Input packet was: " ^ in_packet_string ^ " at port "); print_int in_port; print "\n";
	   print_output_packets output_packets))
       end
       handle ParseError parse_err_msg => TextIO.print_err parse_err_msg
       handle _ =>
	 TextIO.print_err ("Usage: " ^ CommandLine.name() ^ " <n>\n");’;
     in
      ()
     end
    else append_prog o process_topdecs $
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
	   print_output_packets output_packets))
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
fun translate_p4 progname dict actx astate n_max debug_mode =
 let
  val _ =
   if debug_mode
   then
    let
     val actx_debug_def =
      Define ‘actx_debug (n:num) : v1model_ascope' actx' = ^actx’;

     val astate_debug_def =
      Define ‘astate_debug (n:num) : v1model_ascope' astate' = ^astate’;

     val n_max_debug_def =
      Define ‘n_max_debug (n:num) : num = ^n_max’;

     val _ = translate actx_debug_def;

     val _ = translate astate_debug_def;

     val _ = translate n_max_debug_def;



     val p4_append_input_list'_debug_def =
      Define ‘p4_append_input_list'_debug input astate : v1model_ascope' astate' = p4_append_input_list' input astate’;
     val _ = translate p4_append_input_list'_debug_def;

     val p4_get_output_list_debug_def =
      Define ‘p4_get_output_list_debug (astate:v1model_ascope' astate') : ((bool list # num) list) = p4_get_output_list astate’;
     val _ = translate p4_get_output_list_debug_def;

     val get_frame_list_def =
      Define
       ‘get_frame_list (arch_frame_list':arch_frame_list') : frame_list' option =
	 case arch_frame_list' of
         | arch_frame_list'_empty => NONE
         | arch_frame_list'_regular frame_list =>
          SOME frame_list’;
     val _ = translate get_frame_list_def;


     (* TODO: Write these in-line in CakeML *)
     val empty_frame_list_def =
      Define
       ‘empty_frame_list (n:num) : string =
	 "no frames"’;
     val _ = translate empty_frame_list_def;
     val unknown_function_def =
      Define
       ‘unknown_function (n:num) : string =
	 "unknown function"’;
     val _ = translate unknown_function_def;


     val get_funn_string_def =
      Define
       ‘get_funn_string funn' : string option =
         let
          word =
	   (case funn' of
	    | funn'_name func_name => func_name
	    | funn'_inst ext_obj_name => ext_obj_name
	    | funn'_ext ext_obj_name func_name => func_name)
         in
          ALOOKUP ^dict word’;
     val _ = translate get_funn_string_def;

     (* TODO: This is duplicated for both debug and non-debug *)
     val cake_top_exec_def =
      Define
       ‘cake_top_exec (input:(bool list # num)) =
	 (case
	  arch_multi_exec' ^actx
	   (p4_append_input_list' [input] ^astate) ^n_max of
	 | SOME res => SOME res
	 | NONE => NONE) : (v1model_ascope' astate') option’;

     (* TODO: This is the bottleneck... *)
     val _ = translate cake_top_exec_def;

    in
     ()
    end
   else
    let
     val cake_top_exec_def =
      Define
       ‘cake_top_exec input =
	 case
	  arch_multi_exec' ^actx
	   (p4_append_input_list' [input] ^astate) ^n_max of
	 | SOME res => SOME $ p4_get_output_list res
	 | NONE => NONE’;

     (* TODO: This is the bottleneck... *)
     val _ = translate cake_top_exec_def;
    in
     ()
    end

  val prog = append_prog_p4_wrapper debug_mode ();
 in
  astToSexprLib.write_ast_to_file (progname^".sexp") prog
 end
;

end
