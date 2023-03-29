open HolKernel Parse bossLib boolSyntax;
open testutils;
open PPBackEnd;
open parse_jsonTheory;
open petr4_to_hol4p4Theory;

open excluded;

open petr4_to_hol4p4Syntax;

(* For EVAL *)
open ASCIInumbersLib;

(*
(* Flags for determining type of output *)
val unicode = false;
val raw_output = true;
(* Flags used here *)
val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0);
*)

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

fun print_hol4p4_vals valname fmap pblock_map =
 let
  val _ = map print_hol4_val (map (fn (a, b) => (valname^("_"^a), b))
                              [("fmap", fmap), ("pblock_map", pblock_map)])
 in
  ()
 end
;

(* Print test:

 val args = ["1", "2", "filter.json", "filter.log"];
 val args = ["1", "2", "vss_input.json", "vss_input.log"];
 val args = ["1", "2", "test-examples/good/actionAnnotations.json", "test-examples/good/actionAnnotations.log"];

  val outstream = TextIO.openOut "test.txt"
  val _ = TextIO.output (outstream, "test")
  val _ = TextIO.closeOut outstream

*)

fun main() =
 let
  val args = CommandLine.arguments()
 in
  if length args = 4
  then
   let
    val filename = el 3 args;
    val logname = el 4 args;

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
      val vss_parse_clean = EVAL ``p4_from_json ^(rhs $ concl vss_parse_thm)``;
      val final_res_tup = rhs $ concl vss_parse_clean;
     in
      if is_SOME_msg final_res_tup
      then
       let
	val _ = TextIO.outputSubstr (outstream, Substring.full ("OK: Parsed "^(filename^"\n")));
	val _ = TextIO.closeOut outstream;
	(* TODO: Map this result to everything we need...
	 *       Does not use explicit list to map variable names due to warning *)
	val res_list = pairLib.strip_pair $ dest_SOME_msg final_res_tup;
       in
	print_hol4p4_vals valname (el 3 res_list) (el 6 res_list)
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
