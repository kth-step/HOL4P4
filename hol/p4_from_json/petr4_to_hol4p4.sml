open HolKernel Parse bossLib boolSyntax;
open testutils;
open PPBackEnd optionSyntax pairSyntax numSyntax listSyntax;
open parse_jsonTheory;
open petr4_to_hol4p4Theory;

open excluded petr4_to_hol4p4Syntax p4Syntax p4_vssLib p4_ebpfLib;

(* For EVAL *)
open ASCIInumbersLib;

datatype arch = vss | ebpf;

fun parse_arch arch_str =
 if arch_str = "vss"
 then SOME vss
 else if arch_str = "ebpf"
 then SOME ebpf
 else NONE
;

fun arch_to_term arch_opt =
 case arch_opt of
   SOME vss => mk_some arch_vss_NONE_tm
 | SOME ebpf => mk_some arch_ebpf_NONE_tm
 | NONE => mk_none ``:arch_t``
;

(* Returns the astate type of the architecture (as a term) as a string, for outputting *)
fun astate_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then SOME "vss_ascope astate"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then SOME "ebpf_ascope astate"
 else NONE
;

(* TODO: Less code duplication... *)
fun actx_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then SOME "vss_ascope actx"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then SOME "ebpf_ascope actx"
 else NONE
;

(*
(* Flags for determining type of output *)
val unicode = false;
val raw_output = true;
(* Flags used here *)
val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0);
*)

(* TODO: Currently duplicated here form the Ott export. Put type abbreviations in p4Syntax? *)
val _ = type_abbrev("bl", ``:bool list``);
val _ = type_abbrev("in_out", ``:(bl # num)``);

(* Output a HOL4 value to script format *)
(* TODO: Fix format details *)
fun output_hol4_val outstream (name, tm, ty_opt) =
 let
  val _ = TextIO.output (outstream, "val "^name^" = ``");
  val _ = TextIO.output (outstream, term_to_string tm);
  val _ = case ty_opt of
            SOME ty_str => TextIO.output (outstream, ":"^ty_str)
          | NONE => ()
  val _ = TextIO.output (outstream, "``;\n\n");
 in
  ()
 end
;

(* TODO: Replace these with a general solution ASAP *)
val ipv4_header_uninit =
 mk_v_header_list F 
                  [(``"version"``, mk_v_biti_arb 4),
                   (``"ihl"``, mk_v_biti_arb 4),
                   (``"diffserv"``, mk_v_biti_arb 8),
                   (``"totalLen"``, mk_v_biti_arb 16),
                   (``"identification"``, mk_v_biti_arb 16),
                   (``"flags"``, mk_v_biti_arb 3),
                   (``"fragOffset"``, mk_v_biti_arb 13),
                   (``"ttl"``, mk_v_biti_arb 8),
                   (``"protocol"``, mk_v_biti_arb 8),
                   (``"hdrChecksum"``, mk_v_biti_arb 16),
                   (``"srcAddr"``, mk_v_biti_arb 32),
                   (``"dstAddr"``, mk_v_biti_arb 32)];
val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_biti_arb 48),
                   (``"srcAddr"``, mk_v_biti_arb 48),
                   (``"etherType"``, mk_v_biti_arb 16)];
val parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];

fun output_hol4p4_incipit valname outstream =
 let
  val _ = TextIO.output (outstream, "open HolKernel Parse bossLib boolSyntax p4Theory p4_exec_semTheory;\n\n");
  val _ = TextIO.output (outstream, "val _ = new_theory \""^(valname^"\";\n\n"));
 in
  ()
 end
;

fun output_hol4p4_explicit outstream =
 let
  val _ = TextIO.output (outstream, "\n\nval _ = export_theory ();");
 in
  ()
 end
;


datatype stf_iotype = packet | expect;

(* hex_to_bin "DEFEC8" *)
fun hex_to_bin s = 
 let
  fun hex_digit_to_bin c = 
   case c of
     #"0" => "0000"
   | #"1" => "0001"
   | #"2" => "0010"
   | #"3" => "0011"
   | #"4" => "0100"
   | #"5" => "0101"
   | #"6" => "0110"
   | #"7" => "0111"
   | #"8" => "1000"
   | #"9" => "1001"
   | #"A" => "1010"
   | #"B" => "1011"
   | #"C" => "1100"
   | #"D" => "1101"
   | #"E" => "1110"
   | #"F" => "1111"
   | #"a" => "1010"
   | #"b" => "1011"
   | #"c" => "1100"
   | #"d" => "1101"
   | #"e" => "1110"
   | #"f" => "1111"
   | _ => raise Fail ("Invalid hex digit: "^(str c))
 in
  String.concat $ List.map hex_digit_to_bin $ String.explode s
 end
;

fun parse_line s =
 let
  val tokens = String.tokens (fn c => c = #" ") s
  val port = List.nth (tokens, 1)
  val hex_string = String.concat (List.drop (tokens, 2))
  val bin_string = hex_to_bin hex_string
 in
  (port, bin_string)
 end
;

fun parse_packet s =
 case String.tokens (fn c => c = #" ") s of
   "packet" :: rest => SOME (parse_line s)
 | "expect" :: rest => SOME (parse_line s)
 | _ => NONE
;

fun string_to_term s =
 let
  fun char_to_bool c =
   case c of
     #"0" => F
   | #"1" => T
   | _ => raise Fail ("Invalid input: "^s)
 in
  mk_list (List.map char_to_bool $ String.explode s, bool)
 end
;

fun stf_iotype_to_str iot = 
 if iot = packet
 then "packet"
 else "expect"
;

fun output_in_out outstream valname iot n (port, data) =
 let
  val data_tm = string_to_term data
  val port_tm = term_of_int port
  val tm = mk_pair (data_tm, port_tm)
 in
  output_hol4_val outstream (valname^("_"^((stf_iotype_to_str iot)^(Int.toString n))), tm, NONE)
 end
;

fun drop_last l = String.implode $ List.take (explode l, size l - 1);

fun switch iot =
 if iot = packet
 then expect
 else packet
;

(* Should parse to pairs of bits and port number, type abbreviation in_out *)
(* TODO: Here, we should also print the function that performs the test and check *)
local
 fun parse_stf' outstream valname stf_iotype n instream =
  case TextIO.inputLine instream of
    SOME s =>
     (case parse_packet (drop_last s) of
       SOME (port, data) =>
	(case Int.fromString port of
	  SOME i =>
	   let
	    val _ = output_in_out outstream valname stf_iotype n (i, data)
	   in
	    parse_stf' outstream valname (switch stf_iotype) (n+1) instream
	   end
	 | NONE => raise Fail ("Invalid port number: "^port))
     | NONE => parse_stf' outstream valname stf_iotype n instream)
   | NONE => ()
in
 fun parse_stf outstream stfname_opt valname =
  case stfname_opt of
   SOME stfname =>
    let
     val instream = TextIO.openIn stfname;
     val _ = parse_stf' outstream valname packet 1 instream;
     val _ = TextIO.closeIn instream;
    in
     ()
    end
   | NONE => ()
end
;

fun vss_add_ffblocks_to_ab_list ab_list_tm =
 let
  val (ab_list, ab_list_ty) = dest_list ab_list_tm
  val ab_list' = [``arch_block_inp``,
                  (el 1 ab_list),
                  ``arch_block_ffbl "parser_runtime"``,
                  (el 2 ab_list),
                  ``arch_block_ffbl "pre_deparser"``,
                  (el 3 ab_list),
                  ``arch_block_out``]
 in
  (mk_list (ab_list', ab_list_ty))
 end
;

fun ebpf_add_ffblocks_to_ab_list ab_list_tm =
 let
  val (ab_list, ab_list_ty) = dest_list ab_list_tm
  val ab_list' = [``arch_block_inp``,
                  (el 1 ab_list),
                  (el 2 ab_list),
                  ``arch_block_out``]
 in
  (mk_list (ab_list', ab_list_ty))
 end
;

fun output_hol4p4_vals outstream valname stfname_opt fmap pblock_map ab_list_tm arch_opt_tm =
 let
  val actx_astate_opt =
   if (is_arch_vss $ dest_some arch_opt_tm) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ^vss_func_map ^fmap``
     (* TODO: Make appropriate additions to ab_list_tm here *)
     val actx =
      list_mk_pair [vss_add_ffblocks_to_ab_list ab_list_tm, pblock_map, vss_ffblock_map,
                    vss_input_f, vss_output_f,
                    vss_copyin_pbl, vss_copyout_pbl, vss_apply_table_f,
                    vss_ext_map, fmap']
     (* TODO: Move ext_obj_map to p4_vssLib? *)
     val ext_obj_map = ``[(0, INL (core_v_ext_packet_in []));
			  (1, INL (core_v_ext_packet_out []));
			  (2, INL (core_v_ext_packet_out []))]:(num, v_ext) alist``;
     val ascope = list_mk_pair [term_of_int 3,
				ext_obj_map,
                                (* TODO: Initial v_map - hard-coded for now *)
				``[("inCtrl", v_struct [("inputPort", ^(mk_v_biti_arb 4))]);
				   ("outCtrl", v_struct [("outputPort", ^(mk_v_biti_arb 4))]);
				   ("b_in", v_ext_ref 0);
				   ("b_out", v_ext_ref 1);
				   ("data_crc", v_ext_ref 2);
				   ("parsedHeaders", (^parsed_packet_struct_uninit));
				   ("headers", (^parsed_packet_struct_uninit));
				   ("outputHeaders", (^parsed_packet_struct_uninit));
				   ("parseError", v_err "NoError")]:(string, v) alist``,
                                (* TODO: Initial ctrl must be added separately elsewhere *)
				mk_list ([], ``:(string # ((e_list # (string # e_list)) list))``)]
     (* ab index, input list, output list, ascope *)
     val aenv = list_mk_pair [term_of_int 0,
                              (* TODO: Input must be added separately elsewhere *)
                              mk_list ([], ``:in_out``),
                              (* TODO: Output must be added separately elsewhere *)
                              mk_list ([], ``:in_out``), ascope]
     (* aenv, global scope (can be empty since we substitute these in place?), arch_frame_list, status *)
     val astate = list_mk_pair [aenv,
			        mk_list ([``[]:scope``], scope_ty),
			        arch_frame_list_empty_tm,
			        status_running_tm]
    in
     SOME (actx, astate)
    end
   else if (is_arch_ebpf $ dest_some arch_opt_tm) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ^ebpf_func_map ^fmap``
     val actx =
      list_mk_pair [ebpf_add_ffblocks_to_ab_list ab_list_tm, pblock_map, ebpf_ffblock_map,
                    ebpf_input_f, ebpf_output_f,
                    ebpf_copyin_pbl, ebpf_copyout_pbl, ebpf_apply_table_f,
                    ebpf_ext_map, fmap']
     (* TODO: Initialise ext_obj_map... *)
     val ext_obj_map = ``[(0, INL (core_v_ext_packet_in []));
			  (1, INL (core_v_ext_packet_out []))]:(num, v_ext) alist``;
     val ascope = list_mk_pair [term_of_int 2,
				ext_obj_map,
                                (* TODO: Initial v_map - hard-coded for now *)
				``[("packet", v_ext_ref 0);
				   ("headers", v_struct []);
				   ("accept", v_bool ARB);
                                   ("parseError", v_err "NoError")]:(string, v) alist``,
                                (* TODO: Ctrl always starts out totally empty for now *)
				mk_list ([], ``:(string # ((e_list # (string # e_list)) list))``)]
     (* ab index, input list, output list, ascope *)
     val aenv = list_mk_pair [term_of_int 0,
                              (* TODO: Input must be added separately elsewhere *)
                              mk_list ([], ``:in_out``),
                              (* TODO: Output must be added separately elsewhere *)
                              mk_list ([], ``:in_out``), ascope]
     (* aenv, global scope (can be empty since we substitute these in place?), arch_frame_list, status *)
     val astate = list_mk_pair [aenv,
			        mk_list ([``[]:scope``], scope_ty),
			        arch_frame_list_empty_tm,
			        status_running_tm]
    in
     SOME (actx, astate)
    end
   else if (is_none arch_opt_tm) then
    (* TODO *)
    NONE
   else raise Fail ("Unknown architecture");
  val _ = case actx_astate_opt of
           SOME (actx, astate) =>
            map (output_hol4_val outstream) (map (fn (a, b, c) => (valname^("_"^a), b, c))
                              [("actx", actx, actx_of_arch arch_opt_tm), ("astate", astate, astate_of_arch arch_opt_tm)])
          | NONE => [()];
  val _ = parse_stf outstream stfname_opt valname
 in
  ()
 end
;

(* Print test:

 val args = ["1", "2", "filter.json", "filter.log"];
 val args = ["1", "2", "vss_input.json", "vss_input.log", "vss"];
 val args = ["1", "2", "test-examples/good/action_call_ebpf.json", "test-examples/good/action_call_ebpf.log", "ebpf", "Y"];

  val outstream = TextIO.openOut "test.txt"
  val _ = TextIO.output (outstream, "test")
  val _ = TextIO.closeOut outstream

*)

fun main() =
 let
  val args = CommandLine.arguments()
 in
  if length args >= 4
  then
   let
    val filename = el 3 args;
    val logname = el 4 args;
    val arch_opt = if length args >= 5 then parse_arch (el 5 args) else NONE;
    val arch_opt_tm = arch_to_term arch_opt;

    (* NOTE: This will just remove the suffix .json *)
    val valname_no_suffix = List.drop (rev $ explode filename, 5);
    val stfname_opt =
     if length args = 6
     then 
      if (el 6 args) = "Y"
      then SOME ((implode $ rev valname_no_suffix)^".stf")
      else NONE
     else NONE;

    val valname_no_prefix =
     (List.take (valname_no_suffix, Lib.index (fn c => c = #"/") valname_no_suffix))
     handle HOL_ERR _ => valname_no_suffix;
    val valname = implode $ rev $ valname_no_prefix;

    val outstream = TextIO.openAppend logname;
   in
    if not $ exists (fn el => el = valname) (List.concat $ snd $ unzip exclude_descs)
    then
     let
      val instream = TextIO.openIn filename;
      val vss_input_tm = stringLib.fromMLstring $ TextIO.inputAll $ instream;
      val _ = TextIO.closeIn instream;
      (* Lexing + parsing to HOL4 JSON *)
      val vss_parse_thm =
       EVAL ``parse (OUTL (lex (p4_preprocess_str (^vss_input_tm)) ([]:token list))) [] T``;
      (* TODO: Check if result is INR (OK) or INL (print error) *)
      (* Parsing to HOL4P4 JSON *)
      val vss_parse_clean = EVAL ``p4_from_json ^(rhs $ concl vss_parse_thm) ^(arch_opt_tm)``;
      val final_res_tup = rhs $ concl vss_parse_clean;
     in
      if is_SOME_msg final_res_tup
      then
       let
	val _ = TextIO.outputSubstr (outstream, Substring.full ("OK: Parsed "^(filename^"\n")));
	val _ = TextIO.closeOut outstream;
	(* TODO: Map this result to everything we need...
	 *       Does not use explicit list to map variable names due to warning *)
	val res_list = pairLib.spine_pair $ dest_SOME_msg final_res_tup;
       in
        let
         (* TODO: Take this as an argument instead *)
         val outstream = TextIO.openOut "test_out.sml";
         val _ = output_hol4p4_incipit valname outstream ;
(* Debug:
val fmap = (el 5 res_list)
val pblock_map = (el 9 res_list)
val ab_list = (el 11 res_list)
val arch_opt = (el 10 res_list)
*)
         val _ = output_hol4p4_vals outstream valname stfname_opt (el 5 res_list) (el 9 res_list) (el 11 res_list) (el 10 res_list);
         val _ = output_hol4p4_explicit outstream;
         val _ = TextIO.closeOut outstream;
        in
         ()
        end
       end
      else
       let
	val parse_error = stringLib.fromHOLstring $ dest_NONE_msg final_res_tup
         handle HOL_ERR _ => "Parsing of JSON was not completed, yielding a malformed result without error message (you might want to check that EVAL works correctly)";
	val _ = TextIO.outputSubstr (outstream, Substring.full ("FAIL: Could not parse "^filename^(". "^(parse_error^"\n"))));
	val _ = TextIO.closeOut outstream;
       in
	print parse_error
       end
     end
    else
     let
      val desc = case get_error_desc valname exclude_descs of SOME desc' => desc' | NONE => "unknown fix";
      val _ = TextIO.outputSubstr (outstream, Substring.full ("EXCLUDED: "^(filename^" requires "^((desc)^"\n"))));
      val _ = TextIO.closeOut outstream;
     in
      print ""
     end
   end
  else print ("Wrong number of arguments ("^((Int.toString $ length args)^")! Should be target JSON file and log file.\n"))
 end;

val _ = main();

val _ = OS.Process.exit(OS.Process.success);
