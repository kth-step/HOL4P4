open HolKernel Parse bossLib boolSyntax;
open testutils;
open PPBackEnd optionSyntax pairSyntax numSyntax listSyntax;
open parse_jsonTheory;
open petr4_to_hol4p4Theory;

open excluded petr4_to_hol4p4Syntax p4Syntax p4_vssLib p4_ebpfLib p4_v1modelLib;

(* For EVAL *)
open ASCIInumbersLib;

datatype arch = vss | ebpf | v1model;

fun parse_arch arch_str =
 if arch_str = "vss"
 then SOME vss
 else if arch_str = "ebpf"
 then SOME ebpf
 else if arch_str = "v1model"
 then SOME v1model
 else NONE
;

fun arch_to_term arch_opt =
 case arch_opt of
   SOME vss => mk_some arch_vss_NONE_tm
 | SOME ebpf => mk_some arch_ebpf_NONE_tm
 | SOME v1model => mk_some arch_v1model_NONE_tm
 | NONE => mk_none ``:arch_t``
;

fun ascope_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then "``:vss_ascope``"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then "``:ebpf_ascope``"
 else if is_arch_v1model $ dest_some arch_opt_tm
 then "``:v1model_ascope``"
 else "``:'a``"
;

fun astr_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then "vss"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then "ebpf"
 else if is_arch_v1model $ dest_some arch_opt_tm
 then "v1model"
 else raise Fail ("Unknown architecture: "^(term_to_string arch_opt_tm))
;

(* Returns the astate type of the architecture (as a term) as a string, for outputting *)
fun astate_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then SOME "vss_ascope astate"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then SOME "ebpf_ascope astate"
 else if is_arch_v1model $ dest_some arch_opt_tm
 then SOME "v1model_ascope astate"
 else NONE
;

(* TODO: Less code duplication... *)
fun actx_of_arch arch_opt_tm =
 if is_arch_vss $ dest_some arch_opt_tm
 then SOME "vss_ascope actx"
 else if is_arch_ebpf $ dest_some arch_opt_tm
 then SOME "ebpf_ascope actx"
 else if is_arch_v1model $ dest_some arch_opt_tm
 then SOME "v1model_ascope actx"
 else NONE
;

(*
(* Flags for determining type of output *)
val unicode = false;
val raw_output = true;

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

fun output_hol4p4_incipit valname outstream =
 let
  val _ = TextIO.output (outstream, "open HolKernel Parse bossLib boolSyntax;\nopen p4_testLib p4_stfTheory;\n\n");
  val _ = TextIO.output (outstream, "val _ = new_theory \""^(valname^"\";\n\n"));
 in
  ()
 end
;

fun output_hol4p4_explicit outstream =
 let
  val _ = TextIO.output (outstream, "val _ = export_theory ();");
 in
  ()
 end
;

datatype stf_iotype = packet | expect;

(* hex_to_bin "DEFEC8" *)
(* hex_to_bin "C*DE" *)
fun hex_to_bin s = 
 let
  fun hex_digit_to_bin c = 
   case c of
     #"0" => [F, F, F, F]
   | #"1" => [F, F, F, T]
   | #"2" => [F, F, T, F]
   | #"3" => [F, F, T, T]
   | #"4" => [F, T, F, F]
   | #"5" => [F, T, F, T]
   | #"6" => [F, T, T, F]
   | #"7" => [F, T, T, T]
   | #"8" => [T, F, F, F]
   | #"9" => [T, F, F, T]
   | #"A" => [T, F, T, F]
   | #"B" => [T, F, T, T]
   | #"C" => [T, T, F, F]
   | #"D" => [T, T, F, T]
   | #"E" => [T, T, T, F]
   | #"F" => [T, T, T, T]
   | #"a" => [T, F, T, F]
   | #"b" => [T, F, T, T]
   | #"c" => [T, T, F, F]
   | #"d" => [T, T, F, T]
   | #"e" => [T, T, T, F]
   | #"f" => [T, T, T, T]
   | #"*" => [arb, arb, arb, arb]
   | _ => raise Fail ("Invalid hex digit: "^(str c))
 in
  flatten $ List.map hex_digit_to_bin $ String.explode s
 end
;

datatype stf_restype =
 (* packet/expect, port and packet itself *)
   io of stf_iotype * int * term list
 | setdefault of string * string * string * int list
 (* Block name, table name, keys, action name, action arguments *)
 | add of string * string * term * string * int list
 | none;

fun parse_stf_io_line s stf_iotype =
 let
  (* TODO: It seems $ is not needed for the tests we run. Significance unclear *)
  val s' = String.translate (fn c => if c = #"$" then "" else str c) s;
  val tokens = String.tokens (fn c => c = #" ") s'
  val port_str = List.nth (tokens, 1)
  val hex_packet = String.concat $ List.drop (tokens, 2)
  val bool_list_packet = hex_to_bin hex_packet
 in
  case Int.fromString port_str of
   SOME port =>
    io (stf_iotype, port, bool_list_packet)
  | NONE => none
 end
;

(* Splits e.g. "prefix.suffix" into "prefix" and ".suffix" - note nothing is removed *)
fun split_string_gen incl str ch =
 let
  val i_opt =
   SOME (Lib.index (fn c => c = ch) (explode str))
   handle HOL_ERR _ => NONE;
  val i_offset = if incl then 0 else 1
 in
  case i_opt of
    SOME i =>
    (String.substring(str, 0, i), String.substring(str, i + i_offset, size str - i - i_offset))
  | NONE => ("", str)
 end

val split_string_incl = split_string_gen true

val split_string = split_string_gen false

fun ints_from_string []     = SOME []
  | ints_from_string (h::t) =
   case Int.fromString h of
     SOME i =>
     (case ints_from_string t of
        SOME res => SOME (i::res)
      | NONE => NONE)
   | NONE => NONE
;

fun parse_stf_setdefault_line tokens =
 let
  val (block_name, table) = split_string (el 1 tokens) #"."
  (* Note that arguments are no longer separated by whitespaces in "action" *)
  (* TODO: Generalise this, so global actions can also be used? *)
  val (_, action) = split_string (String.concat (tl tokens)) #"."
  val (action_name, args) = split_string_incl action #"("
  val args_list = String.tokens (fn ch => ch = #",") (String.substring(args, 1, size args - 2))
  (* TODO: Different number formats? *)
  val args_list' = map (fn tok => snd (split_string tok #":")) args_list
 in
  case ints_from_string args_list' of
    SOME ints =>
     setdefault (block_name, table, action_name, ints)
  | NONE => none
 end
;

(* Parses a list of hex strings in the format "0x0004FFFF" into HOL4P4 bitv values *)
fun parse_keys [] = []
 |  parse_keys (h::t) =
  let
   (* TODO: Fields are assumed to be in order *)
   val (field_name, hex_str) = split_string h #":"
   val hex_str' = String.extract (hex_str, 2, NONE)
   val bin_str = hex_to_bin hex_str'
   val bitv_tm = mk_e_v $ mk_v_bit (mk_pair (mk_list (bin_str, bool), term_of_int $ length bin_str))
  in
   (bitv_tm::parse_keys t)
  end
;

fun parse_stf_add_line tokens =
 let
  (* Split up tokens into table, keys, and action *)
  (* Rewritten to avoid exhaustiveness warning *)
  val table_token = el 1 tokens
  val priority_token = el 2 tokens
  val rest_tokens = List.drop (tokens, 2)
  val (key_tokens, rest_tokens2) = foldr (fn (a, (b, c)) => if String.isPrefix "key." a then ((String.extract (a, 4, NONE))::b, c) else (b, a::c)) ([],[]) rest_tokens
  val action_token = String.concat rest_tokens2

  (* Get block and table name *)
  val (block_name, table) = split_string table_token #"."

  (* TODO: No actual type inference takes place here, we just assume the input has the correct
   *       leading zeroes *)
  val keys = mk_list (parse_keys key_tokens, e_ty)

  (* Note that arguments are no longer separated by whitespaces in "action" *)
  (* TODO: Generalise this, so global actions can also be used? *)
  val (_, action) = split_string action_token #"."
  val (action_name, args) = split_string_incl action #"("
  val args_list = String.tokens (fn ch => ch = #",") (String.substring(args, 1, size args - 2))
  (* TODO: Different number formats? *)
  val args_list' = map (fn tok => snd (split_string tok #":")) args_list
 in
  case ints_from_string args_list' of
    SOME ints =>
     add (block_name, table, keys, action_name, ints)
  | NONE => none
 end
;

(* TODO: pay forward rest instead of s? *)
(*
val s = "setdefault pipe.t pipe.Reject(rej:0, bar:1)"
*)
fun parse_stf_line s =
 case String.tokens (fn c => c = #" ") s of
   "packet" :: rest => parse_stf_io_line s packet
 | "expect" :: rest => parse_stf_io_line s expect
 | "add" :: rest => parse_stf_add_line rest
 | "setdefault" :: rest => parse_stf_setdefault_line rest
 | _ => none
;

fun stf_iotype_to_str iot = 
 if iot = packet
 then "packet"
 else "expect"
;

fun output_in_out outstream valname n (iot, port, data) =
 let
  val data_tm = mk_list (data, bool)
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

(* TODO: Should dest_SOME be used directly or via some wrapper, to give a sensible error message? *)
fun output_actx_setdefault outstream valname block_name table_name action_name args =
 let
  val outstring =
   String.concat ["val ", valname, "_actx = optionSyntax.dest_some $ rhs $ concl $ EVAL ``p4_replace_tbl_default ^",
                  valname, "_actx", " \"",
                  block_name, "\" \"",
                  table_name, "\" \"",
                  action_name, "\" ",
                  args, "``;\n\n"]
  val _ = TextIO.output (outstream, outstring);
 in
  ()
 end
;

fun output_astate_add outstream valname arch_opt table_name keys action_name args =
 let
  val outstring =
   String.concat ["val ", valname, "_astate = optionSyntax.dest_some $ rhs $ concl $ EVAL ``",
                  (astr_of_arch arch_opt)^"_add_ctrl ^",
                  valname, "_astate", " \"",
                  table_name, "\" ",
                  term_to_string keys, " \"",
                  action_name, "\" ",
                  args, "``;\n\n"]
  val _ = TextIO.output (outstream, outstring);
 in
  ()
 end
;

fun output_test_astate outstream valname n =
 let
  val outstring = String.concat ["val ", valname, "_test", Int.toString n, "_astate = rhs $ concl $ EVAL ``p4_replace_input ^", valname, "_packet", Int.toString n, " ^", valname, "_astate``;\n\n"]
  val _ = TextIO.output (outstream, outstring);
 in
  ()
 end
;

fun process_arbs' [] acc (vars, l') = (vars, l', acc)
  | process_arbs' (h::t) acc (vars, l') =
    if is_arb h
    then
     let
      val var = mk_var("b_"^(int_to_string acc), bool)
     in
      process_arbs' t (acc + 1) (vars@[var], l'@[var])
     end
    else process_arbs' t acc (vars, l'@[h]);
(*
fun process_arbs (l: term list) =
 (fn (a,b,c) => (mk_list (a, bool), mk_list (b, bool))) (process_arbs' l 0 ([], []));
*)
fun process_arbs_list (ll: term list list) acc_init =
 let
  fun process_arbs_list' [] acc (vars, data) = (vars, data, acc)
    | process_arbs_list' (h::t) acc (vars, data) =
     let
      val (vars', data', n_vars) = process_arbs' h acc ([], [])
     in
      process_arbs_list' t (acc+n_vars) (vars@vars', data@[data'])
     end
 in
  (fn (a,b,c) => (a, map (fn c => mk_list (c, bool)) b, c)) (process_arbs_list' ll acc_init ([], []))
 end;

(*
(* Row breaks for legibility *)
fun output_test_theorem outstream valname arch_opt n (out_port, out_data) =
 let
  val (vars, out_data') = process_arbs out_data
  val actx = (valname^"_actx")
  val _ = TextIO.output (outstream, "Theorem "^(valname^("_test"^((Int.toString n)^":\n"))));
  val _ = TextIO.output (outstream, "?n ab_index' ");
  val _ = TextIO.output (outstream, term_to_string vars);
  val _ = TextIO.output (outstream, " ascope' g_scope_list' arch_frame_list' status'.\n");
  val _ = TextIO.output (outstream, "arch_multi_exec ^"^(actx^(" ^"^(valname^("_test"^((Int.toString n)^"_astate n =\n"))))));
  val _ = TextIO.output (outstream, " SOME ((ab_index', [], [("^((Int.toString out_port)^(", "^((term_to_string out_data')^")], ascope'), g_scope_list', arch_frame_list', status')\n"))));
  val _ = TextIO.output (outstream, "Proof\n");
  val _ = TextIO.output (outstream, "p4_eval_test_tac "^((ascope_of_arch arch_opt)^" "^(valname^("_actx "^(valname^"_test"^((Int.toString n)^"_astate\n"))))));
  val _ = TextIO.output (outstream, "QED\n\n");
 in
  ()
 end
;

fun output_test_reject_theorem outstream valname arch_opt n =
 let
  val actx = (valname^"_actx")
  val _ = TextIO.output (outstream, "Theorem "^(valname^("_test"^((Int.toString n)^":\n"))));
  val _ = TextIO.output (outstream, "?n ab_index' ascope' g_scope_list' arch_frame_list' status'.\n");
  val _ = TextIO.output (outstream, "arch_multi_exec ^"^(actx^(" ^"^(valname^("_test"^((Int.toString n)^"_astate n =\n"))))));
  val _ = TextIO.output (outstream, " SOME ((ab_index', [], [], ascope'), g_scope_list', arch_frame_list', status')\n");
  val _ = TextIO.output (outstream, "Proof\n");
  val _ = TextIO.output (outstream, "p4_eval_test_tac "^((ascope_of_arch arch_opt)^" "^(valname^("_actx "^(valname^"_test"^((Int.toString n)^"_astate\n"))))));
  val _ = TextIO.output (outstream, "QED\n\n");
 in
  ()
 end
;
*)

fun terms_to_string [] = ""
  | terms_to_string (h::t) =
 let
  val str = term_to_string h
 in
 (str^(" "^(terms_to_string t)))
 end

(* Row breaks for legibility *)
(* TODO: Naming convention of bits could be i/o + n + _ + b + _ m, where i/o is input or output, n is its number in the order, an m is the bit position *)
fun output_test_list_theorem outstream valname arch_opt (input_list:(int * term list) list, output_list) =
 let
  val (in_vars, in_data', i) = process_arbs_list (map snd input_list) 0
  val (out_vars, out_data', i') = process_arbs_list (map snd output_list) i
  val in_packets = mk_list ((map mk_pair (zip in_data' (map (term_of_int o fst) input_list))), “:(bool list # num)”);
  val out_packets = mk_list ((map mk_pair (zip out_data' (map (term_of_int o fst) output_list))), “:(bool list # num)”);

  (* Output astate with updated input separately *)
  val astate_input_update =
   String.concat ["val ", valname, "_astate = rhs $ concl $ EVAL “(p4_append_input_list ",
                  (term_to_string in_packets), " ^",
                  valname, "_astate)”;\n\n"];
  val _ = TextIO.output (outstream, astate_input_update);

  (* Output theorem *)
  val actx = (valname^"_actx")
  val _ = TextIO.output (outstream, "Theorem "^(valname^("_test"^(":\n"))));
  val _ =
   if null in_vars
   then ()
   else 
    let
     val _ = TextIO.output (outstream, "! ");
     val _ = TextIO.output (outstream, terms_to_string in_vars);
     val _ = TextIO.output (outstream, ".\n");
    in
     ()
    end

  val theorem =
   String.concat ["?n ab_index' ", terms_to_string out_vars,
                  "ascope' g_scope_list' arch_frame_list' status'.\n",
                  "arch_multi_exec ^", actx, " ^",
                  valname, "_astate",
                  (* ("(p4_append_input_list "^(term_to_string in_packets)^(" ^"^(valname^("_astate)")))), *)
                  " n =\n", " SOME ((ab_index', [], ", (term_to_string out_packets),
                  ", ascope'), g_scope_list', arch_frame_list', status')\n",
                  "Proof\n", "p4_eval_test_tac ", (ascope_of_arch arch_opt),
                  " ", valname, "_actx ", valname, "_astate\n",
                  "QED\n\n"];
  val _ = TextIO.output (outstream, theorem);

(*
  val _ = TextIO.output (outstream, "?n ab_index' ");
  val _ = TextIO.output (outstream, terms_to_string out_vars);
  val _ = TextIO.output (outstream, "ascope' g_scope_list' arch_frame_list' status'.\n");
  val state_str = ("(p4_append_input_list "^(term_to_string in_packets)^(" ^"^(valname^("_astate)"))));
  val _ = TextIO.output (outstream, "arch_multi_exec ^"^(actx^(" "^(state_str^(" n =\n")))));
  val _ = TextIO.output (outstream, " SOME ((ab_index', [], "^((term_to_string out_packets)^", ascope'), g_scope_list', arch_frame_list', status')\n"));
  val _ = TextIO.output (outstream, "Proof\n");
  val _ = TextIO.output (outstream, "p4_eval_test_tac "^((ascope_of_arch arch_opt)^" "^(valname^("_actx "^(valname^("_astate\n"))))));
  val _ = TextIO.output (outstream, "QED\n\n");
*)
 in
  ()
 end
;

fun infer_args (ftymap, blftymap) block_name action_name args =
 let
  val inferred_args = rhs $ concl $ EVAL ``p4_infer_args (^ftymap, ^blftymap) ^(stringSyntax.fromMLstring block_name) ^(stringSyntax.fromMLstring action_name) ^(listSyntax.mk_list(map term_of_int args, num))``
 in
  if (is_some inferred_args)
  then SOME (dest_some inferred_args)
  else NONE
 end
;

fun to_hol_list_string l =
 let
  val rev_l = rev l
  val l_semis = map (fn str => str^"; ") (tl rev_l)
 in
  "["^((concat (rev ((hd l)::(l_semis))))^"]")
 end
;

(* Should parse to pairs of bits and port number, type abbreviation in_out *)
(* TODO: Here, we should also print the function that performs the test and check *)
local
 fun parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list, output_list) instream =
  case TextIO.inputLine instream of
    SOME s =>
     (case parse_stf_line (drop_last s) of
       (* Using result from parse_stf_setdefault_line: *)
       setdefault (block_name, table_name, action_name, args) =>
        (case infer_args (ftymap, blftymap) block_name action_name args of
           SOME args_term =>
	   let
	    val _ = output_actx_setdefault outstream valname block_name table_name action_name (term_to_string args_term)
	   in
	    parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list, output_list) instream
	   end
        (* TODO: Raise exception or print error message to output? *)
         | NONE => raise Fail ("Could not parse action arguments in setdefault stf command"))
     | add (block_name, table_name, keys, action_name, args) =>
        (case infer_args (ftymap, blftymap) block_name action_name args of
           SOME args_term =>
	   let
	    val _ = output_astate_add outstream valname arch_opt_tm table_name keys action_name (term_to_string args_term)
	   in
	    parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list, output_list) instream
	   end
        (* TODO: Raise exception or print error message to output? *)
         | NONE => raise Fail ("Could not parse action arguments in add stf command"))
     | io (stf_iotype, port, data) =>
      if stf_iotype = packet
      then
       parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list@[(port, data)], output_list) instream
      else
       parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list, output_list@[(port, data)]) instream
(*
        (case prev_line_opt of
           NONE =>
          (* TODO: Check that parsed_stf_iotype is "packet"? *)
          parse_stf' (ftymap, blftymap) outstream valname expect arch_opt_tm n (SOME (parsed_stf_iotype, port, data)) instream
         | SOME prev_stf_line =>
	  if parsed_stf_iotype = expect
	  then
           (* Print packet-expect theorem *)
	   let
	    val _ = output_in_out outstream valname n prev_stf_line
	    val _ = output_test_astate outstream valname n
	    val _ = output_test_theorem outstream valname arch_opt_tm n (port, data)
	   in
	    parse_stf' (ftymap, blftymap) outstream valname packet arch_opt_tm (n+1) NONE instream
	   end
	  else
           (* Print packet-reject theorem *)
	   let
	    val _ = output_in_out outstream valname n prev_stf_line
	    val _ = output_test_astate outstream valname n
	    val _ = output_test_reject_theorem outstream valname arch_opt_tm n
	   in
	    parse_stf' (ftymap, blftymap) outstream valname packet arch_opt_tm (n+1) (SOME (parsed_stf_iotype, port, data)) instream
	   end)
*)
     | none => parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm (input_list, output_list) instream)
   | NONE =>
    let
     val _ = output_test_list_theorem outstream valname arch_opt_tm (input_list, output_list)
    in
     ()
    end
in
 fun parse_stf outstream stfname_opt valname (ftymap, blftymap) arch_opt_tm =
  case stfname_opt of
   SOME stfname =>
    let
     val instream = TextIO.openIn stfname;
     (* TODO: Write _packetn and _rejectm terms almost as before, but now indexed separately. 
              Write only a single new astate and following theorem at the end, which
              has all input packets in the input queue in order and all outputs in the
              output queue in order. *)
     val _ = parse_stf' (ftymap, blftymap) outstream valname arch_opt_tm ([],[]) instream;
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

fun v1model_add_ffblocks_to_ab_list ab_list_tm =
 let
  val (ab_list, ab_list_ty) = dest_list ab_list_tm
  val ab_list' = [``arch_block_inp``,
                  (el 1 ab_list),
                  ``arch_block_ffbl "postparser"``,
                  (el 2 ab_list),
                  (el 3 ab_list),
                  (el 4 ab_list),
                  (el 5 ab_list),
                  (el 6 ab_list),
                  ``arch_block_out``]
 in
  (mk_list (ab_list', ab_list_ty))
 end
;

fun output_hol4p4_vals outstream valname stfname_opt (ftymap, blftymap) fmap pblock_map ab_list_tm arch_opt_tm =
 let
  val actx_astate_opt =
   if (is_arch_vss $ dest_some arch_opt_tm) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ^vss_func_map ^fmap``
     (* TODO: Make appropriate additions to ab_list_tm here *)
     val actx =
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [vss_add_ffblocks_to_ab_list ab_list_tm, pblock_map, vss_ffblock_map,
		     vss_input_f, vss_output_f,
		     vss_copyin_pbl, vss_copyout_pbl, vss_apply_table_f,
		     vss_ext_map, fmap']
     val init_ctrl = rhs $ concl $ EVAL ``vss_init_ctrl ^pblock_map``;
     val ascope = list_mk_pair [term_of_int 3,
				vss_init_ext_obj_map,
                                vss_init_v_map,
                                init_ctrl]
     (* ab index, input list, output list, ascope *)
     (* Note: Input is added later elsewhere *)
     val aenv = list_mk_pair [term_of_int 0,
                              mk_list ([], ``:in_out``),
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
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [ebpf_add_ffblocks_to_ab_list ab_list_tm, pblock_map, ebpf_ffblock_map,
		     ebpf_input_f, ebpf_output_f,
		     ebpf_copyin_pbl, ebpf_copyout_pbl, ebpf_apply_table_f,
		     ebpf_ext_map, fmap']
     val init_ctrl = rhs $ concl $ EVAL ``ebpf_init_ctrl ^pblock_map``;
     val ascope = list_mk_pair [ebpf_init_counter,
				ebpf_init_ext_obj_map,
                                ebpf_init_v_map,
                                init_ctrl]
     (* ab index, input list, output list, ascope *)
     (* Note: Input is added later elsewhere *)
     val aenv = list_mk_pair [term_of_int 0,
                              mk_list ([], ``:in_out``),
                              mk_list ([], ``:in_out``), ascope]
     (* aenv, global scope (can be empty since we substitute these in place?), arch_frame_list, status *)
     val astate = list_mk_pair [aenv,
			        mk_list ([``[]:scope``], scope_ty),
			        arch_frame_list_empty_tm,
			        status_running_tm]
    in
     SOME (actx, astate)
    end
   else if (is_arch_v1model $ dest_some arch_opt_tm) then
    let
     val fmap' = rhs $ concl $ EVAL ``AUPDATE_LIST ^v1model_func_map ^fmap``
     val actx =
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [v1model_add_ffblocks_to_ab_list ab_list_tm, pblock_map, v1model_ffblock_map,
		     v1model_input_f, v1model_output_f,
		     v1model_copyin_pbl, v1model_copyout_pbl, v1model_apply_table_f,
		     v1model_ext_map, fmap']
     val init_ctrl = rhs $ concl $ EVAL ``v1model_init_ctrl ^pblock_map``;
     val ascope = list_mk_pair [v1model_init_counter,
				v1model_init_ext_obj_map,
                                v1model_init_v_map,
                                init_ctrl]
     (* ab index, input list, output list, ascope *)
     (* Note: Input is added later elsewhere *)
     val aenv = list_mk_pair [term_of_int 0,
                              mk_list ([], ``:in_out``),
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
  val _ = parse_stf outstream stfname_opt valname (ftymap, blftymap) arch_opt_tm
 in
  ()
 end
;

(* Replaces characters to create a valid prefix for HOL4 variable names *)
fun format_for_hol4 (str: string) : string =
    String.translate (fn c => if c = #"-" then "_" else (String.str c)) str;

(* Print test:
 (* OK *)
 val args = ["1", "2", "test-examples/ebpf_stf_only/action_call_table_ebpf.json", "test-examples/ebpf_stf_only/action_call_table_ebpf.log", "test-examples/ebpf_stf_only/action_call_table_ebpfScript.sml", "ebpf", "Y"];
 (* OK *)
 val args = ["1", "2", "test-examples/ebpf_stf_only/action_call_ebpf.json", "test-examples/ebpf_stf_only/action_call_ebpf.log", "test-examples/ebpf_stf_only/action_call_ebpfScript.sml", "ebpf", "Y"];

 val args = ["1", "2", "test-examples/ebpf_stf_only/key_ebpf.json", "test-examples/ebpf_stf_only/key_ebpf.log", "test-examples/ebpf_stf_only/key_ebpfScript.sml", "ebpf", "Y"];

 val args = ["1", "2", "test-examples/stf_only/bvec-hdr-bmv2.json", "test-examples/stf_only/bvec-hdr-bmv2.log", "test-examples/stf_only/bvec-hdr-bmv2Script.sml", "v1model", "Y"];

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
    val scriptname = el 5 args;
    val arch_opt = if length args >= 6 then parse_arch (el 6 args) else NONE;
    val arch_opt_tm = arch_to_term arch_opt;

    (* NOTE: This will just remove the suffix .json *)
    val valname_no_suffix = List.drop (rev $ explode filename, 5);
    val stfname_opt =
     if length args = 7
     then 
      if (el 7 args) = "Y"
      then SOME ((implode $ rev valname_no_suffix)^".stf")
      else NONE
     else NONE;

    val valname_no_prefix =
     (List.take (valname_no_suffix, Lib.index (fn c => c = #"/") valname_no_suffix))
     handle HOL_ERR _ => valname_no_suffix;
    val valname = format_for_hol4 $ implode $ rev $ valname_no_prefix;

    val outstream = TextIO.openAppend logname;
   in
    if not $ exists (fn el => el = valname) (List.concat $ snd $ unzip exclude_descs)
    then
     let
      val instream = TextIO.openIn filename;
      (* TODO: Rename *)
      val vss_input_tm = stringLib.fromMLstring $ TextIO.inputAll $ instream;
      val _ = TextIO.closeIn instream;
      (* Lexing + parsing to HOL4 JSON *)
      (* TODO: Rename *)
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
         val outstream = TextIO.openOut scriptname;
         val _ = output_hol4p4_incipit valname outstream;
(* Debug:
val (ftymap, blftymap) = (el 4 res_list, el 5 res_list)
val fmap = (el 6 res_list)
val pblock_map = (el 10 res_list)
val ab_list_tm = (el 12 res_list)
val arch_opt_tm = (el 11 res_list)
*)
         val _ = output_hol4p4_vals outstream valname stfname_opt (el 4 res_list, el 5 res_list) (el 6 res_list) (el 10 res_list) (el 12 res_list) (el 11 res_list);
         val _ = output_hol4p4_explicit outstream;
         val _ = TextIO.closeOut outstream;
        in
         ()
        end
       end
      else
       let
	val parse_error = stringLib.fromHOLstring $ dest_NONE_msg final_res_tup
         handle HOL_ERR _ => "Parsing of JSON was not completed, yielding a incompletely reduced RHS without error message (you might want to check that EVAL works correctly)";
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
