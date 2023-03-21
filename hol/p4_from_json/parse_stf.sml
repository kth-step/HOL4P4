open HolKernel Parse bossLib boolSyntax listSyntax pairSyntax numSyntax;
open testutils;
open PPBackEnd mlibUseful;
open excluded;

(* val exclude_descs = []:((string * string list) list); *)

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

fun drop_last l = String.implode $ List.take (explode l, size l - 1);

fun parse_packet s =
 case String.tokens (fn c => c = #" ") (drop_last s) of
   "packet" :: rest => SOME (parse_line s)
 | "expect" :: rest => SOME (parse_line s)
 | _ => NONE
;

(*
val input = ["packet 0 00000000 00000000 00000000 00000000 00000000 ABCDEF01",
             "expect 0 00000000 00000000 00000000 00000000 00000000 ABCDEF01",
             "packet 0 001b1700 0130b881 98b7aeb7 08004500 00344a6f 40004006 53920a01 98453212 c86acf2c 01bbd0fa 585c4ccc b2ac8010 0353c314 00000101 080a0192 463911a0 c06f",
             "expect 0 001b1700 0130b881 98b7aeb7 08004500 00344a6f 40004006 53920a01 98453212 c86acf2c 01bbd0fa 585c4ccc b2ac8010 0353c314 00000101 080a0192 463911a0 c06f",
             "packet 0 00000000 00000000 00000000 00000000 00000000 00010000",
             "expect 0 00000000 00000000 00000000 00000000 00000000 00010000",
             "packet 0 00000000 00000000 00000000 00000000 00000000 00011000",
             "expect 0 00000000 00000000 00000000 00000000 00000000 00011000",
             "packet 0 001b1700 0130b881 98b7aeb7 08004500 00344a6f 40004006 53920a01 98453212 c86acf2c 01bbd0fa 585c4ccc b2ac8010 0353c314 00000101 080a0192 463911a0 c06e",
             "expect 0 001b1700 0130b881 98b7aeb7 08004500 00344a6f 40004006 53920a01 98453212 c86acf2c 01bbd0fa 585c4ccc b2ac8010 0353c314 00000101 080a0192 463911a0 c06e"]
*)

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

fun print_in_out (port, data) =
 let
  val data_tm = string_to_term data
  val port_tm = term_of_int port
 in
  term_to_string (mk_pair (data_tm, port_tm))
 end
;

(* Should parse to pairs of bits and port number, type abbreviation in_out *)
(* TODO: Here, we should also print the function that performs the test and check *)
fun parse_stf instream =
 case TextIO.inputLine instream of
   SOME s =>
    (case parse_packet s of
      SOME (port, data) =>
       (case Int.fromString port of
         SOME i =>
          let
           val _ = print_in_out (i, data)
          in
           parse_stf instream
          end
        | NONE => raise Fail ("Invalid port number: "^port))
    | NONE => parse_stf instream)
  | NONE => ()
;

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
      val _ = TextIO.openIn filename
      val _ = parse_stf (TextIO.openIn filename)
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
