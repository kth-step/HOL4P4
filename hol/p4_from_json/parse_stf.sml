open HolKernel Parse bossLib boolSyntax listSyntax pairSyntax numSyntax;
open testutils;
open PPBackEnd mlibUseful;
open excluded;

(* val exclude_descs = []:((string * string list) list); *)

(* For debugging:
fun read_file filename =
  let
    val instream = TextIO.openIn filename
    fun read_lines instream =
      case TextIO.inputLine instream of
        NONE => []
      | SOME line => line :: read_lines instream
    val lines = read_lines instream
    val _ = TextIO.closeIn instream
  in
    lines
  end
;

val test_line = el 1 (read_file "test-examples/good/action_call_ebpf.stf")
*)

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

(* Print a HOL4 value to script format *)
(* TODO: Fix format details *)
(* TODO: Duplicated from parse_any_test, put in shared lib *)
fun print_hol4_val (name, tm) =
 let
  val _ = print ("val "^name^" = ``");
  val _ = print_term tm
  val _ = print ("``;\n\n");
 in
  ()
 end
;

fun stf_iotype_to_str iot = 
 if iot = packet
 then "packet"
 else "expect"
;

fun print_in_out valname iot n (port, data) =
 let
  val data_tm = string_to_term data
  val port_tm = term_of_int port
  val tm = mk_pair (data_tm, port_tm)
 in
  print_hol4_val (valname^("_"^((stf_iotype_to_str iot)^(Int.toString n))), tm)
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
(* TODO: Make wrapper *)
fun parse_stf valname stf_iotype n instream =
 case TextIO.inputLine instream of
   SOME s =>
    (case parse_packet (drop_last s) of
      SOME (port, data) =>
       (case Int.fromString port of
         SOME i =>
          let
           val _ = print_in_out valname stf_iotype n (i, data)
          in
           parse_stf valname (switch stf_iotype) (n+1) instream
          end
        | NONE => raise Fail ("Invalid port number: "^port))
    | NONE => parse_stf valname stf_iotype n instream)
  | NONE => ()
;

(* Print test:

 val args = ["1", "2", "test-examples/good/action_call_ebpf.stf", "teststf.log"];

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

    (* NOTE: This will just remove the suffix .stf - only works in same dir *)
    val valname_no_suffix = List.drop (rev $ explode filename, 4);
    val valname_no_prefix =
     case index (fn c => c = #"/") valname_no_suffix of
       NONE => valname_no_suffix 
     | SOME i => (List.take (valname_no_suffix, i));
    val valname = implode $ rev $ valname_no_prefix;

    val outstream = TextIO.openAppend logname;
   in
    if not $ List.exists (fn el => el = valname) (List.concat $ snd $ unzip exclude_descs)
    then
     let
      val instream = TextIO.openIn filename
      val _ = parse_stf valname packet 1 instream
      val _ = TextIO.closeOut outstream;
     in
      ()
     end
    else
     let
      val desc = case get_error_desc valname exclude_descs of SOME desc' => desc' | NONE => "unknown .stf exclusion reason";
      val _ = TextIO.outputSubstr (outstream, Substring.full ("EXCLUDED: "^(filename^" requires "^((desc)^"\n"))));
      val _ = TextIO.closeOut outstream;
     in
      print ""
     end
   end
  else print ("Wrong number of arguments ("^((Int.toString $ length args)^")! Should be target .stf file and log file.\n"))
 end;

val _ = main();

val _ = OS.Process.exit(OS.Process.success);
