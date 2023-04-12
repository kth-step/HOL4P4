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
   SOME vss => arch_vss_NONE_tm
 | SOME ebpf => arch_ebpf_NONE_tm
 | SOME _ => raise Fail ("Unknown architecture")
 | NONE => mk_none ``:arch_t``
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

(* Print a HOL4 value to script format *)
(* TODO: Fix format details *)
fun print_hol4_val (name, tm) =
 let
  val _ = print ("val "^name^" = ``");
  val _ = print_term tm
  val _ = print ("``;\n\n");
 in
  ()
 end
;

(*

val test = ``SOME (arch_vss (SOME vss_pkg_VSS))``
can dest_arch_vss $ dest_some test

*)

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

fun print_hol4p4_vals valname fmap pblock_map ab_list arch_opt =
 let
  val ctx_aenv_opt =
   if (can dest_arch_vss $ dest_some arch_opt) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ^vss_func_map ^fmap``
     val actx =
      list_mk_pair [ab_list, pblock_map, vss_ffblock_map, vss_input_f, vss_output_f,
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
			        mk_list ([], scope_ty),
			        arch_frame_list_empty_tm,
			        status_running_tm]
    in
     SOME (actx, astate)
    end
   else if (can dest_arch_ebpf $ dest_some arch_opt) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ebpf_func_map fmap``
     val actx =
      list_mk_pair [ab_list, pblock_map, ebpf_ffblock_map, ebpf_input_f, ebpf_output_f,
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
				   ("accept", v_bool ARB)]:(string, v) alist``,
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
			        mk_list ([], scope_ty),
			        arch_frame_list_empty_tm,
			        status_running_tm]
    in
     SOME (actx, astate)
    end
   else if (can dest_none arch_opt) then
    (* TODO *)
    NONE
   else raise Fail ("Unknown architecture");
  val _ = map print_hol4_val (map (fn (a, b) => (valname^("_"^a), b))
                              [("fmap", fmap), ("pblock_map", pblock_map)]);
 in
  ()
 end
;

(* Print test:

 val args = ["1", "2", "filter.json", "filter.log"];
 val args = ["1", "2", "vss_input.json", "vss_input.log"];
 val args = ["1", "2", "test-examples/good/action_call_ebpf.json", "test-examples/good/action_call_ebpf.log"];

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
    val arch_opt = if length args = 5 then parse_arch (el 5 args) else NONE;
    val arch_opt_tm = arch_to_term arch_opt;

    (* NOTE: This will just remove the suffix .json *)
    val valname_no_suffix = List.drop (rev $ explode filename, 5);
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
	print_hol4p4_vals valname (el 4 res_list) (el 8 res_list) (el 9 res_list) (el 10 res_list)
       end
      else
       let
	val parse_error = stringLib.fromHOLstring $ dest_NONE_msg final_res_tup
         handle HOL_ERR _ => "something exceptional happened";
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
