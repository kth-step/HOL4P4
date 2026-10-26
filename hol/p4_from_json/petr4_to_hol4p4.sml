open HolKernel Parse bossLib boolSyntax;
open PPBackEnd optionSyntax pairSyntax numSyntax listSyntax stringLib;
open parse_jsonTheory;
open petr4_to_hol4p4Theory;

open excluded petr4_to_hol4p4Syntax p4Syntax p4_vssLib p4_ebpfLib p4_v1modelLib;

(* For EVAL *)
(* ASCIInumbersLib is loaded for its side effect of adding the ASCII/number conversions to the EVAL compset *)
local open ASCIInumbersLib in end;
(* intReduce adds integer arithmetic, used to fold compile-time constants *)
local open intReduce in end;

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

(* Returns the astate type of the architecture (as a term) as a string, for output *)
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

(* TODO: Use this everywhere? *)
fun eval_rhs tm = rhs $ concl $ EVAL tm;

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
  val _ = TextIO.output (outstream, "Theory "^valname^"\nAncestors\n  p4_arch_aux petr4_to_hol4p4 p4_exec_sem[qualified]\nLibs\n  p4_testLib\n\n");
 in
  ()
 end
;

fun output_hol4p4_explicit outstream =
 let
  (* export_theory is implicit with the Theory header *)
  val _ = ();
 in
  ()
 end
;

datatype stf_iotype = packet | expect;

(* hex_to_bin "DEFEC8" *)
(* hex_to_bin "C*DE" *)
(* NOTE: This is later treated by process_arbs_list *)
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
 (* packet/expect, port, packet itself and whether it ends with $ *)
   io of stf_iotype * int * term list * bool
 (* Block name, table name, action name, action arguments *)
 | setdefault of string * string * string * term
 (* Table name, key condition on e_l, priority, action name, action arguments *)
 | add of string * term * int * string * term
 | none;

fun parse_stf_io_line s stf_iotype =
 let
  val exact = Char.contains s #"$"
  val s' = String.translate (fn c => if c = #"$" then "" else str c) s;
  val tokens = String.tokens (fn c => c = #" ") s'
  val port_str = List.nth (tokens, 1)
  val hex_packet = String.concat $ List.drop (tokens, 2)
  val bool_list_packet = hex_to_bin hex_packet
 in
  case Int.fromString port_str of
   SOME port =>
    io (stf_iotype, port, bool_list_packet, exact)
  | NONE => raise Fail ("Invalid port in STF command: "^s)
 end
;

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

(* Splits e.g. "prefix.mid.suffix" into "prefix" and ".mid.suffix" *)
val split_string_incl = split_string_gen true

(* Splits e.g. "prefix.mid.suffix" into "prefix" and "mid.suffix" *)
val split_string = split_string_gen false

val reverse_string = implode o List.rev o explode

(* Splits e.g. "prefix.mid.suffix" into "prefix.mid" and "suffix" *)
fun split_string_rev s c =
 let
  val (a,b) = (fn (a,b) => (reverse_string b, reverse_string a)) (split_string (reverse_string s) c)
 in
  if b = ""
  then (b, a)
  else (a,b)
 end

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

fun switch iot =
 if iot = packet
 then expect
 else packet
;

(* TODO: Should dest_SOME be used directly or via some wrapper, to give a sensible error message? *)
fun output_actx_setdefault outstream (actx_name, prev_actx_name) block_name table_name action_name args =
 let
  val outstring =
   String.concat ["val ", actx_name, " = optionSyntax.dest_some $ rhs $ concl $ EVAL ``p4_replace_tbl_default ^",
                  prev_actx_name, " \"",
                  block_name, "\" \"",
                  table_name, "\" \"",
                  action_name, "\" ",
                  args, "``;\n\n"]
  val _ = TextIO.output (outstream, outstring);
 in
  ()
 end
;

fun output_astate_add outstream valname arch_opt table_name keys priority action_name args =
 let
  val outstring =
   String.concat ["val ", valname, "_astate = optionSyntax.dest_some $ rhs $ concl $ EVAL ``",
                  (astr_of_arch arch_opt)^"_add_ctrl ^",
                  valname, "_astate", " \"",
                  table_name, "\" ",
                  "((\\e_l. ", term_to_string keys, "), ", Int.toString priority, ":num) \"",
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

fun terms_to_string [] = ""
  | terms_to_string (h::t) =
 let
  val str = term_to_string h
 in
 (str^(" "^(terms_to_string t)))
 end

fun infer_args (ftymap, blftymap) is_default block_name action_name args =
 let
  val inferred_args =
   eval_rhs ``case p4_infer_args (^ftymap, ^blftymap) ^(stringSyntax.fromMLstring block_name) ^(stringSyntax.fromMLstring action_name) ^(listSyntax.mk_list(map (fn i => mk_numeral (Arbnum.fromString (IntInf.toString i))) args, num)) of | SOME args => SOME ([e_v (v_bool T); e_v (v_bool ^(if is_default then F else T))]++args) | NONE => NONE``
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

(* Parses an STF number (decimal, 0x or 0b, * for don't-care digits) into value and don't-care bits *)
fun parse_stf_num str =
 let
  fun digit_val c =
   if Char.isDigit c then ord c - ord #"0"
   else if Char.isHexDigit c then ord (Char.toLower c) - ord #"a" + 10
   else ~1
  fun parse_digits radix ds =
   if ds = ""
   then raise Fail ("Invalid number in STF file: "^str)
   else
    foldl (fn (c, (v, dc)) =>
            if c = #"*"
            then (v * radix, dc * radix + radix - 1)
            else if 0 <= digit_val c andalso IntInf.fromInt (digit_val c) < radix
            then (v * radix + IntInf.fromInt (digit_val c), dc * radix)
            else raise Fail ("Invalid number in STF file: "^str))
          (0:IntInf.int, 0:IntInf.int) (explode ds)
 in
  if String.isPrefix "0x" str orelse String.isPrefix "0X" str
  then parse_digits 16 (String.extract (str, 2, NONE))
  else if String.isPrefix "0b" str orelse String.isPrefix "0B" str
  then parse_digits 2 (String.extract (str, 2, NONE))
  else if List.all Char.isDigit (explode str)
  then parse_digits 10 str
  else raise Fail ("Invalid number in STF file: "^str)
 end
;

fun parse_stf_exact_num str =
 case parse_stf_num str of
   (v, 0) => v
 | _ => raise Fail ("Don't-care digits are not allowed here in STF file: "^str)
;

fun int_to_bits n (v:IntInf.int) =
 List.tabulate (n, fn i => if IntInf.andb (IntInf.~>> (v, Word.fromInt (n - 1 - i)), 1) = 1 then T else F)
;

fun count_leading_ones [] = 0
  | count_leading_ones (h::t) = if Teq h then 1 + count_leading_ones t else 0
;

(* Splits s at the first occurrence of sep *)
fun split_string_at sep s =
 let
  val (a, b) = Substring.position sep (Substring.full s)
 in
  if Substring.isEmpty b
  then NONE
  else SOME (Substring.string a, String.extract (Substring.string b, size sep, NONE))
 end
;

(* Parses the value of an STF key into a set and its priority (the prefix length for LPM keys) *)
fun parse_stf_key_value tau mk value_str =
 if is_tau_bool tau
 then
  let
   val v = parse_stf_exact_num value_str
  in
   if v = 0 then (``s_sing (v_bool F)``, 0)
   else if v = 1 then (``s_sing (v_bool T)``, 0)
   else raise Fail ("Invalid boolean key value in STF file: "^value_str)
  end
 else if is_tau_bit tau
 then
  let
   val n = dest_tau_bit tau
   val full = IntInf.<< (1, Word.fromInt n) - 1
   val (v, mask) =
    case split_string_at "&&&" value_str of
      SOME (v_str, mask_str) => (parse_stf_exact_num v_str, parse_stf_exact_num mask_str)
    | NONE =>
     (case split_string_at "/" value_str of
        SOME (v_str, len_str) =>
         let
          val len = IntInf.toInt (parse_stf_exact_num len_str)
         in
          if len > n
          then raise Fail ("Prefix length exceeds key width in STF file: "^value_str)
          else (parse_stf_exact_num v_str, full - (IntInf.<< (1, Word.fromInt (n - len)) - 1))
         end
      | NONE =>
       let
        val (v', dont_care) = parse_stf_num value_str
       in
        (v', IntInf.andb (full, IntInf.notb dont_care))
       end)
   val _ =
    if v > full orelse mask > full
    then raise Fail ("Key value wider than the key in STF file: "^value_str)
    else ()
   val n_tm = term_of_int n
   val v_bits = mk_list (int_to_bits n v, bool)
   val mask_bits = int_to_bits n mask
   val prio = if term_eq mk ``mk_lpm`` then count_leading_ones mask_bits else 0
  in
   if mask = full
   then (``s_sing (v_bit (^v_bits, ^n_tm))``, prio)
   else (``s_mask (^v_bits, ^n_tm) (^(mk_list (mask_bits, bool)), ^n_tm)``, prio)
  end
 else raise Fail ("Unsupported key type in STF file: "^(term_to_string tau))
;

(* Matches STF keys by name as p4c's STF drivers do (common prefix, key.fieldN on eBPF) *)
fun parse_stf_keys arch_opt_tm ttymap table_name key_tokens =
 let
  val local_name = snd $ split_string_rev table_name #"."
  val qual_infos_opt = eval_rhs ``ALOOKUP ^ttymap ^(stringSyntax.fromMLstring table_name)``
  val key_infos_opt = if is_some qual_infos_opt then qual_infos_opt else eval_rhs ``ALOOKUP ^ttymap ^(stringSyntax.fromMLstring local_name)``
  val key_infos =
   if is_some key_infos_opt
   then map strip_pair $ fst $ dest_list $ dest_some key_infos_opt
   else raise Fail ("Could not find the keys of table "^table_name)
  val key_names = map (fromHOLstring o hd) key_infos
  val indices = List.tabulate (length key_names, I)
  fun field_index name =
   let
    val field = snd $ split_string_rev name #"."
   in
    if is_arch_ebpf (dest_some arch_opt_tm) andalso String.isPrefix "field" field
    then Int.fromString (String.extract (field, 5, NONE))
    else NONE
   end
  fun key_index name =
   case List.filter (fn i => List.nth (key_names, i) = name) indices of
     [i] => i
   | _ =>
    (case List.filter (fn i => let val k = List.nth (key_names, i) in
                                k <> "" andalso (String.isSuffix ("."^k) name orelse String.isSuffix ("."^name) k) end) indices of
       [i] => i
     | [] =>
      (case field_index name of
         SOME i => if i < length key_names then i else raise Fail ("Unknown key "^name^" of table "^table_name^" in STF file")
       | NONE => raise Fail ("Unknown key "^name^" of table "^table_name^" in STF file"))
     | _ => raise Fail ("Ambiguous key "^name^" of table "^table_name^" in STF file"))
  val named_values =
   map (fn tok =>
         case split_string_at ":" tok of
           SOME (name, value) => (key_index name, value)
         | NONE => raise Fail ("Invalid key "^tok^" of table "^table_name^" in STF file")) key_tokens
  val matches =
   map (fn i =>
         case (List.nth (key_infos, i), List.filter (fn (j, _) => j = i) named_values) of
           ([_, mk, tau], [(_, value)]) => parse_stf_key_value tau mk value
         | ([_, mk, tau], []) =>
          if term_eq mk ``mk_exact``
          then raise Fail ("Missing exact key "^(List.nth (key_names, i))^" of table "^table_name^" in STF file")
          else (``s_univ``, 0)
         | _ => raise Fail ("Duplicate key "^(List.nth (key_names, i))^" of table "^table_name^" in STF file")) indices
  val s_tms = map fst matches
  val keys_tm =
   if List.all (fn s_tm => is_comb s_tm andalso term_eq (rator s_tm) ``s_sing``) s_tms
   then ``e_l = ^(mk_list (map (fn s_tm => mk_comb (``e_v``, rand s_tm)) s_tms, ``:e``))``
   else ``match_all_e e_l ^(mk_list (s_tms, ``:s``))``
 in
  (keys_tm, foldl Int.max 0 (map snd matches), List.all (fn l => term_eq (el 2 l) ``mk_exact`` orelse term_eq (el 2 l) ``mk_lpm``) key_infos)
 end
;

(* Orders the named arguments of an STF action as its parameters (inlined action prefix removed) *)
fun parse_stf_action_args (pblock_map, fmap) block_name action_name args_str =
 let
  val params_opt = eval_rhs ``p4_action_param_names ^pblock_map ^fmap ^(stringSyntax.fromMLstring block_name) ^(stringSyntax.fromMLstring action_name)``
  val params =
   if is_some params_opt
   then List.filter (fn x => x <> "from_table$" andalso x <> "hit$")
         (map (fn x => snd $ split_string_rev (fromHOLstring x) #".") $ fst $ dest_list $ dest_some params_opt)
   else raise Fail ("Could not find action "^action_name^" in STF file")
  val args =
   map (fn tok =>
         case split_string_at ":" (String.translate (fn c => if Char.isSpace c then "" else str c) tok) of
           SOME arg => arg
         | NONE => raise Fail ("Invalid argument "^tok^" of action "^action_name^" in STF file"))
       (String.tokens (fn c => c = #",") args_str)
  val _ =
   if length args = length params
   then ()
   else raise Fail ("Wrong number of arguments of action "^action_name^" in STF file")
 in
  map (fn x =>
        case List.filter (fn (y, _) => y = x) args of
          [(_, v)] => parse_stf_exact_num v
        | _ => raise Fail ("Missing or duplicate argument "^x^" of action "^action_name^" in STF file")) params
 end
;

(* Splits a table name in an STF file into its block and the qualified table name *)
(* TODO: This checks first prefix is a top-level block or not: the import tool should reject
 * programs with instance names equal to top-level block names for this to work *)
fun stf_table_block pblock_map table_token =
 let
  val (block_name, table) =
   if is_none $ eval_rhs “ALOOKUP ^pblock_map ^(stringSyntax.fromMLstring $ fst $ split_string table_token #".")”
   then
    let
     val pbl_name_opt = eval_rhs “p4_pblock_of_tbl ^(stringSyntax.fromMLstring table_token) ^pblock_map”
    in
     if is_some pbl_name_opt
     then (fromHOLstring $ dest_some pbl_name_opt, table_token)
     else raise Fail ("Could not find table "^(table_token^" in pblock_map"))
    end
   else split_string table_token #"."
 in
  (block_name, block_name^("."^table))
 end
;

(* Removes the optional block prefix of an action name in an STF file *)
fun stf_action_name pblock_map action_token =
 let
  val (prefix, action) = split_string action_token #"."
 in
  if Teq $ eval_rhs ``IS_SOME $ ALOOKUP ^pblock_map ^(stringSyntax.fromMLstring prefix)``
  then action
  else if prefix <> "" then (prefix^("."^action)) else action
 end
;

(* Splits an STF table command into the part before the action arguments and the arguments *)
fun split_stf_action cmd =
 case split_string_at "(" cmd of
   SOME (pre, rest) =>
    (case split_string_at ")" rest of
       SOME (args, _) => (pre, args)
     | NONE => raise Fail ("Invalid STF command: "^cmd))
 | NONE => raise Fail ("Invalid STF command: "^cmd)
;

fun parse_stf_setdefault_line (pblock_map, fmap, ftymap, blftymap) cmd =
 let
  val (pre, args_str) = split_stf_action cmd
  val (table_token, action_token) =
   case String.tokens Char.isSpace pre of
     [table_token, action_token] => (table_token, action_token)
   | _ => raise Fail ("Invalid STF setdefault command: "^cmd)
  val (block_name, table) = stf_table_block pblock_map table_token
  val action_name = stf_action_name pblock_map action_token
  val args = parse_stf_action_args (pblock_map, fmap) block_name action_name args_str
 in
  case infer_args (ftymap, blftymap) true block_name action_name args of
    SOME args_tm => setdefault (block_name, table, action_name, args_tm)
  | NONE => raise Fail ("Could not parse action arguments in setdefault stf command")
 end
;

fun parse_stf_add_line arch_opt_tm (pblock_map, fmap, ftymap, blftymap, ttymap) cmd =
 let
  val (pre, args_str) = split_stf_action cmd
  val (table_token, tokens) =
   case String.tokens Char.isSpace pre of
     (table_token::tokens) => (table_token, tokens)
   | [] => raise Fail ("Invalid STF add command: "^cmd)
  val (prio_opt, tokens') =
   case tokens of
     (h::t) => if List.all Char.isDigit (explode h) then (Int.fromString h, t) else (NONE, tokens)
   | [] => (NONE, tokens)
  val (key_tokens, action_token) =
   case rev tokens' of
     (action_token::rev_key_tokens) => (rev rev_key_tokens, action_token)
   | [] => raise Fail ("Invalid STF add command: "^cmd)
  val (block_name, table) = stf_table_block pblock_map table_token
  val (keys_tm, key_prio, lpm_only) = parse_stf_keys arch_opt_tm ttymap table key_tokens
  (* The longest prefix wins in tables with only lpm and exact keys, otherwise the largest STF priority *)
  val prio = if lpm_only then key_prio else (case prio_opt of SOME p => Int.max (1, 10000 - p) | NONE => 0)
  val action_name = stf_action_name pblock_map action_token
  val args = parse_stf_action_args (pblock_map, fmap) block_name action_name args_str
 in
  case infer_args (ftymap, blftymap) false block_name action_name args of
    SOME args_tm => add (table, keys_tm, prio, action_name, args_tm)
  | NONE => raise Fail ("Could not parse action arguments in add stf command")
 end
;

fun drop_stf_word s =
 Substring.string $ Substring.dropl Char.isSpace $ Substring.dropl (not o Char.isSpace) $ Substring.dropl Char.isSpace $ Substring.full s
;

fun parse_stf_line arch_opt_tm (pblock_map, fmap, ftymap, blftymap, ttymap) s =
 case String.tokens Char.isSpace s of
   [] => none
 | "packet" :: rest => parse_stf_io_line s packet
 | "expect" :: rest => parse_stf_io_line s expect
 | "add" :: rest => parse_stf_add_line arch_opt_tm (pblock_map, fmap, ftymap, blftymap, ttymap) (drop_stf_word s)
 | "setdefault" :: rest => parse_stf_setdefault_line (pblock_map, fmap, ftymap, blftymap) (drop_stf_word s)
 | ["wait"] => none
 | _ => raise Fail ("Unsupported STF command: "^s)
;

fun stf_add_to_string (table_name, keys, priority, action_name, args) =
 String.concat ["(\"", table_name, "\", ((\\e_l. ", term_to_string keys, "), ",
                Int.toString priority, ":num), \"", action_name, "\", ", term_to_string args, ")"]
;

(* The test theorem with one run per phase, each from the final state of the previous one *)
fun output_test_phases_theorem outstream valname arch_opt (phases:(string * (string * term * int * string * term) list * (int * term list) list * (int * term list * bool) list) list) =
 let
  val inputs = List.concat (map #3 phases)
  val outputs = List.concat (map #4 phases)
  val (in_vars, in_data', i) = process_arbs_list (map snd inputs) 0
  val (out_vars, out_data', i') = process_arbs_list (map #2 outputs) i
  val tails = List.tabulate (length outputs, fn k =>
               if #3 (List.nth (outputs, k)) then NONE
               else SOME (mk_var ("tail_"^(int_to_string k), mk_list_type bool)))
  val out_data'' = map (fn (d, tail_opt) => case tail_opt of SOME t => mk_append (d, t) | NONE => d) (zip out_data' tails)
  val out_vars' = out_vars@(List.mapPartial I tails)
  val in_packets = map mk_pair (zip in_data' (map (term_of_int o fst) inputs))
  val out_packets = mk_list ((map mk_pair (zip out_data'' (map (term_of_int o #1) outputs))), “:(bool list # num)”);
  fun phase_inputs [] _ = []
    | phase_inputs ((_, _, ins, _)::t) l =
     (mk_list (List.take (l, length ins), “:(bool list # num)”))::(phase_inputs t (List.drop (l, length ins)))
  val phases' = zip phases (phase_inputs phases in_packets)
  val _ = TextIO.output (outstream,
           String.concat ["val ", valname, "_astate = rhs $ concl $ EVAL “(p4_append_input_list ",
                          term_to_string (snd $ hd phases'), " ^", valname, "_astate)”;\n\n"])
  fun state_vars j = String.concat [" outl", j, " ascope", j, " g", j, " status", j]
  fun final_state j = String.concat ["((0, [], outl", j, ", ascope", j, "), g", j, ", arch_frame_list_empty, status", j, ")"]
  fun start_state j (upds, ins_tm) =
   if j = 1
   then "^"^valname^"_astate"
   else
    let
     val j' = Int.toString (j - 1)
    in
     String.concat ["(THE (add_ctrl_list_gen ((0, ", term_to_string ins_tm, ", outl", j', ", ascope", j', "), g", j', ", arch_frame_list_empty, status", j', ")\n  [",
                    String.concatWith ";\n   " (map stf_add_to_string upds), "]))"]
    end
  val conjs =
   map (fn (j, ((actx_name, upds, _, _), ins_tm)) =>
         String.concat ["arch_multi_exec ^", actx_name, " ", start_state j (upds, ins_tm), " n", Int.toString j, " =\n",
                        " SOME ", final_state (Int.toString j)]) (zip (List.tabulate (length phases, fn j => j + 1)) phases')
  val vars = String.concatWith " " (List.tabulate (length phases, fn j => "n"^(Int.toString (j + 1))^(state_vars (Int.toString (j + 1)))))
  val _ = TextIO.output (outstream, "Theorem "^(valname^("_test"^(":\n"))));
  val _ =
   if null in_vars
   then ()
   else TextIO.output (outstream, "! "^(terms_to_string in_vars)^".\n")
  val theorem =
   String.concat ["?", vars, " ", terms_to_string out_vars', ".\n",
                  String.concatWith " /\\\n" conjs, " /\\\n",
                  "outl", Int.toString (length phases), " = ", term_to_string out_packets, "\n",
                  "Proof\n", "p4_eval_test_tac ", (ascope_of_arch arch_opt), "\n",
                  "QED\n\n"];
  val _ = TextIO.output (outstream, theorem);
 in
  ()
 end
;

fun is_stf_update cmd =
 case cmd of
   io _ => false
 | _ => true
;

fun is_stf_packet cmd =
 case cmd of
   io (packet, _, _, _) => true
 | _ => false
;

(* Groups STF commands into phases: a table update after a packet starts a new phase *)
local
 fun stf_phases' [] (upds, ios) = [(upds, ios)]
   | stf_phases' (cmd::cmds) (upds, ios) =
    if is_stf_update cmd andalso List.exists is_stf_packet ios
    then (upds, ios)::(stf_phases' cmds ([cmd], []))
    else if is_stf_update cmd
    then stf_phases' cmds (upds@[cmd], ios)
    else stf_phases' cmds (upds, ios@[cmd])
in
 fun stf_phases cmds =
  case rev (stf_phases' cmds ([], [])) of
    ((upds, ios)::(upds', ios')::phases) =>
     if List.exists is_stf_packet ios
     then rev ((upds, ios)::(upds', ios')::phases)
     else rev ((upds', ios'@ios)::phases)
  | phases => rev phases
end
;

(* Should parse to pairs of bits and port number, type abbreviation in_out *)
local
 fun read_stf_cmds arch_opt_tm maps instream =
  case TextIO.inputLine instream of
    SOME line =>
     let
      val s = String.translate (fn c => if c = #"\n" orelse c = #"\r" then "" else str c) line
      val s' = case split_string_at "#" s of SOME (s', _) => s' | NONE => s
     in
      case parse_stf_line arch_opt_tm maps s' of
        none => read_stf_cmds arch_opt_tm maps instream
      | cmd => cmd::(read_stf_cmds arch_opt_tm maps instream)
     end
  | NONE => []

 fun ios_of ios =
  (List.mapPartial (fn cmd => case cmd of io (packet, port, data, exact) => SOME (port, data) | _ => NONE) ios,
   List.mapPartial (fn cmd => case cmd of io (expect, port, data, exact) => SOME (port, data, exact) | _ => NONE) ios)

 (* Outputs a phase's table updates: setdefault into the actx, add into the astate or the theorem *)
 fun output_phase_upds outstream valname arch_opt_tm (j, (upds, ios)) (actx_name, acc) =
  let
   val actx_name' = if j = 1 orelse List.all (fn cmd => case cmd of setdefault _ => false | _ => true) upds
                    then actx_name else valname^"_actx"^(Int.toString j)
   val (_, adds) =
    foldl (fn (cmd, (prev_actx_name, adds)) =>
            case cmd of
              setdefault (block_name, table_name, action_name, args_tm) =>
               let
                val _ = output_actx_setdefault outstream (actx_name', prev_actx_name) block_name table_name action_name (term_to_string args_tm)
               in
                (actx_name', adds)
               end
            | add (table_name, keys_tm, priority, action_name, args_tm) =>
              if j = 1
              then
               let
                val _ = output_astate_add outstream valname arch_opt_tm table_name keys_tm priority action_name (term_to_string args_tm)
               in
                (prev_actx_name, adds)
               end
              else (prev_actx_name, adds@[(table_name, keys_tm, priority, action_name, args_tm)])
            | _ => (prev_actx_name, adds)) (actx_name, []) upds
   val (inputs, outputs) = ios_of ios
  in
   (actx_name', acc@[(actx_name', adds, inputs, outputs)])
  end
in
 fun parse_stf outstream stfname_opt valname maps arch_opt_tm =
  case stfname_opt of
   SOME stfname =>
    let
     val instream = TextIO.openIn stfname;
     val cmds = read_stf_cmds arch_opt_tm maps instream;
     val _ = TextIO.closeIn instream;
     val phases = stf_phases cmds
     val (_, phases') =
      foldl (fn (phase, res) => output_phase_upds outstream valname arch_opt_tm phase res)
            (valname^"_actx", []) (zip (List.tabulate (length phases, fn j => j + 1)) phases)
    in
     output_test_phases_theorem outstream valname arch_opt_tm phases'
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
                  (el 1 ab_list), (* Parser *)
                  ``arch_block_ffbl "postparser"``,
                  (el 2 ab_list), (* VerifyChecksum *)
                  (el 3 ab_list), (* Ingress *)
                  (el 4 ab_list), (* Egress *)
                  (el 5 ab_list), (* ComputeChecksum *)
                  (el 6 ab_list), (* Deparser *)
                  ``arch_block_out``]
 in
  (mk_list (ab_list', ab_list_ty))
 end
;

fun vss_add_param_vars_to_v_map init_v_map tau =
 let
  val uninit_H_val_tm = eval_rhs “zero_val_from_tau ^tau”
 in
  eval_rhs “AUPDATE_LIST ^init_v_map [("parsedHeaders", ^uninit_H_val_tm);
                                      ("headers", ^uninit_H_val_tm);
                                      ("outputHeaders", ^uninit_H_val_tm)]”
 end
;

fun ebpf_add_param_vars_to_v_map init_v_map tau =
 let
  val uninit_H_val_tm = eval_rhs “zero_val_from_tau ^tau”
 in
  eval_rhs “AUPDATE_LIST ^init_v_map [("headers", ^uninit_H_val_tm)]”
 end
;

fun tie_ext_insts k0 top_inits pblock_map =
 let
  val res = eval_rhs ``p4_tie_ext_insts ^k0 ^top_inits ^pblock_map``
  val (n, res') = dest_pair res
  val (g_scope_ties, res'') = dest_pair res'
  val (pblock_map', insts) = dest_pair res''
 in
  (n, g_scope_ties, pblock_map', fst $ dest_list insts)
 end
;

(* Runs each constructor once on the initial state *)
fun construct_ext_objs ext_map stop_consts n insts ascope =
 let
  fun construct (inst, ascope) =
   let
    val (k, inst') = dest_pair inst
    val (ext_name, args) = dest_pair inst'
    val ext_name_str = stringLib.fromHOLstring ext_name
    fun fail msg = raise Fail ("extern object "^(ext_name_str^(" at index "^((term_to_string k)^(": "^msg)))))
    val (params, ctor) =
     case total (dest_pair o dest_some o fst o dest_pair o dest_some) (eval_rhs ``ALOOKUP ^ext_map ^ext_name``) of
       SOME res => res
     | NONE => fail "no constructor in the extern map of the architecture"
    val param_names = map (stringLib.fromHOLstring o fst o dest_pair) (fst $ dest_list params)
    val _ = if not (null param_names) andalso hd param_names = "this" then () else fail "constructor without a \"this\" parameter"
    val arg_tms = fst $ dest_list args
    val _ = if length arg_tms = length param_names - 1 then () else fail "wrong number of constructor arguments"
    fun arg_val e =
     case total dest_some (eval_rhs ``exp_to_val ([]:scope) ^e``) of
       SOME v => v
     | NONE => fail ("constructor argument is not a compile-time constant: "^(term_to_string e))
    fun mk_entry (name, v) = mk_pair (``varn_name ^(stringLib.fromMLstring name)``, mk_pair (v, ``NONE:lval option``))
    val scope = mk_list (mk_entry ("this", ``v_bot``)::(map mk_entry (zip (tl param_names) (map arg_val arg_tms))), ``:(varn # (v # lval option))``)
    val scope_list = mk_list ([scope], scope_ty)
    val (ascope', res') =
     case total (dest_pair o dest_some) (rhs $ concl $ computeLib.RESTR_EVAL_CONV stop_consts ``^ctor (^ascope, []:g_scope_list, ^scope_list)``) of
       SOME res => res
     | NONE => fail "constructor failed"
    val (scope_list', _) = dest_pair res'
    val k' =
     case total (dest_v_ext_ref o dest_some) (eval_rhs ``lookup_lval ^scope_list' (lval_varname (varn_name "this"))``) of
       SOME k' => k'
     | NONE => fail "constructor did not assign an extern object reference to \"this\""
    val _ = if term_eq k k' then () else fail ("constructed at index "^(term_to_string k'))
   in
    ascope'
   end
  val ascope' = foldl construct ascope insts
  val counter = fst $ dest_pair ascope'
  val _ = if term_eq counter n then () else raise Fail ("allocation counter after constructing the extern objects is "^((term_to_string counter)^(", expected "^(term_to_string n))))
 in
  ascope'
 end
;

fun output_hol4p4_vals outstream output_extra_maps valname stfname_opt (ftymap, blftymap) fmap pblock_map tbl_updates_tm arch_opt_tm ab_list_tm ttymap_tm pblock_action_names_map_tm oracle_index top_inits =
 let
  val extra_terms =
   if output_extra_maps
   then [("blftymap", blftymap, SOME "(string, ((funn, (p_tau list # p_tau)) alist)) alist"),
         ("ftymap", ftymap, SOME "((funn, (p_tau list # p_tau)) alist)"),
         ("pblock_action_names_map", pblock_action_names_map_tm, SOME "((string, ((string, string list) alist)) alist)")]
   else []

  (* NOTE: gen_apply_result is a hard-coded "ghost variable" that can't be used in an
   * imported program. This is not accessed before assignment, and so can be concretized
   * without ambiguity *)
  val gscope_init_vars = “[(varn_name "gen_apply_result", (v_struct [("hit", v_bool F);
                            ("miss", v_bool T);
                            ("action_run", v_bit (REPLICATE 32 F, 32))], NONE:lval option))]”

  fun init_g_scope_list g_scope_ties = mk_list ([eval_rhs ``(^gscope_init_vars):scope ++ ^g_scope_ties``], scope_ty)

  (* TODO: Note this is a free variable *)
  val random_oracle_tm = “random_oracle”

  (* TODO: Eliminate code duplication here... *)
  val actx_astate_opt =
   if (is_arch_vss $ dest_some arch_opt_tm) then
    let
     val fmap' = eval_rhs ``AUPDATE_LIST ^vss_func_map ^fmap``
     val (n_tm, g_scope_ties, pblock_map', insts) = tie_ext_insts vss_init_counter top_inits pblock_map
     (* TODO: Make appropriate additions to ab_list_tm here *)
     val actx =
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [vss_add_ffblocks_to_ab_list ab_list_tm, pblock_map', vss_ffblock_map,
		     mk_comb (vss_input_f, n_tm), vss_output_f,
		     vss_copyin_pbl, vss_copyout_pbl, vss_apply_table_f,
		     vss_ext_map, fmap',
                     “vss_get_oracle_index”, “vss_set_oracle_index”,
                     random_oracle_tm]
     val init_ctrl_opt = eval_rhs ``vss_init_ctrl ^pblock_map ^tbl_updates_tm``
(*
     val _ = print ("pblock_map :"^((term_to_string pblock_map)^"\n"))
     val _ = print ("tbl_updates :"^((term_to_string tbl_updates_tm)^"\n"))
*)
    in
     if is_some init_ctrl_opt
     then
      let
       val init_ctrl = dest_some init_ctrl_opt
       (* Here, the initial v_map is completed with the type-parameterized variables *)
       val vss_init_v_map' = vss_add_param_vars_to_v_map vss_init_v_map (dest_vss_pkg_VSS $ dest_some $ dest_arch_vss $ dest_some arch_opt_tm)
       val ascope = construct_ext_objs vss_ext_map vss_construct_stop_consts n_tm insts $
                    list_mk_pair [vss_init_counter,
				  vss_init_ext_obj_map,
				  vss_init_v_map',
				  init_ctrl,
                                  oracle_index]
       (* ab index, input list, output list, ascope *)
       (* Note: Input is added later elsewhere *)
       val aenv = list_mk_pair [term_of_int 0,
				mk_list ([], ``:in_out``),
				mk_list ([], ``:in_out``), ascope]
       (* aenv, global scope (can be empty since we substitute these in place?), arch_frame_list, status *)
       val astate = list_mk_pair [aenv,
				  init_g_scope_list g_scope_ties,
				  arch_frame_list_empty_tm,
				  status_running_tm]
      in
       SOME (actx, astate)
      end
     else raise Fail ("Could not initialise control plane configuration for "^valname)
    end
   else if (is_arch_ebpf $ dest_some arch_opt_tm) then
    let
     val fmap' = eval_rhs ``AUPDATE_LIST ^ebpf_func_map ^fmap``
     val (n_tm, g_scope_ties, pblock_map', insts) = tie_ext_insts ebpf_init_counter top_inits pblock_map
     val actx =
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [ebpf_add_ffblocks_to_ab_list ab_list_tm, pblock_map', ebpf_ffblock_map,
		     mk_comb (ebpf_input_f, n_tm), ebpf_output_f,
		     ebpf_copyin_pbl, ebpf_copyout_pbl, ebpf_apply_table_f,
		     ebpf_ext_map, fmap',
                     “ebpf_get_oracle_index”, “ebpf_set_oracle_index”,
                     random_oracle_tm]
     val init_ctrl_opt = eval_rhs ``ebpf_init_ctrl ^pblock_map ^tbl_updates_tm``;
(*
     val _ = print ("pblock_map :"^((term_to_string pblock_map)^"\n"))
     val _ = print ("tbl_updates :"^((term_to_string tbl_updates_tm)^"\n"))
*)
    in
     if is_some init_ctrl_opt
     then
      let
       val init_ctrl = dest_some init_ctrl_opt
       (* Here, the initial v_map is completed with the type-parameterized variables *)
       val ebpf_init_v_map' = ebpf_add_param_vars_to_v_map ebpf_init_v_map (dest_ebpf_pkg_ebpfFilter $ dest_some $ dest_arch_ebpf $ dest_some arch_opt_tm)
       val ascope = construct_ext_objs ebpf_ext_map ebpf_construct_stop_consts n_tm insts $
                    list_mk_pair [ebpf_init_counter,
				  ebpf_init_ext_obj_map,
				  ebpf_init_v_map',
				  init_ctrl,
                                  oracle_index]
       (* ab index, input list, output list, ascope *)
       (* Note: Input is added later elsewhere *)
       val aenv = list_mk_pair [term_of_int 0,
				mk_list ([], ``:in_out``),
				mk_list ([], ``:in_out``), ascope]
       (* aenv, global scope (can be empty since we substitute these in place?), arch_frame_list, status *)
       val astate = list_mk_pair [aenv,
				  init_g_scope_list g_scope_ties,
				  arch_frame_list_empty_tm,
				  status_running_tm]
      in
       SOME (actx, astate)
      end
     else raise Fail ("Could not initialise control plane configuration for "^valname)
    end
   else if (is_arch_v1model $ dest_some arch_opt_tm) then
    let
     val fmap' = eval_rhs ``AUPDATE_LIST ^v1model_func_map ^fmap``
     val tparams = eval_rhs “(\ (tau1, tau2). (zero_val_from_tau tau1, zero_val_from_tau tau2)) ^(mk_pair (dest_v1model_pkg_V1Switch $ dest_some $ dest_arch_v1model $ dest_some arch_opt_tm))”
     val (n_tm, g_scope_ties, pblock_map', insts) = tie_ext_insts v1model_init_counter top_inits pblock_map
     val v1model_input_f = “v1model_input_f ^n_tm ^tparams”
     val actx =
      rhs $ concl $ SIMP_CONV list_ss [] $
       list_mk_pair [v1model_add_ffblocks_to_ab_list ab_list_tm, pblock_map', v1model_ffblock_map,
		     v1model_input_f, v1model_output_f,
		     v1model_copyin_pbl, v1model_copyout_pbl, v1model_apply_table_f,
		     v1model_ext_map, fmap',
                     “v1model_get_oracle_index”, “v1model_set_oracle_index”,
                     random_oracle_tm]
     val init_ctrl_opt = eval_rhs ``v1model_init_ctrl ^pblock_map ^tbl_updates_tm``;
(*
     val _ = print ("pblock_map :"^((term_to_string pblock_map)^"\n"))
     val _ = print ("tbl_updates :"^((term_to_string tbl_updates_tm)^"\n"))
*)
    in
     if is_some init_ctrl_opt
     then
      let
       val init_ctrl = dest_some init_ctrl_opt
       (* ctrl and persistent extern objects are initialised from the onset *)
       val ascope = construct_ext_objs v1model_ext_map v1model_construct_stop_consts n_tm insts $
                    list_mk_pair [v1model_init_counter,
				  v1model_init_ext_obj_map,
				  v1model_init_v_map,
				  init_ctrl,
                                  oracle_index]
       (* ab index, input list, output list, ascope *)
       (* Note: Input is added later elsewhere *)
       val aenv = list_mk_pair [term_of_int 0,
				mk_list ([], ``:in_out``),
				mk_list ([], ``:in_out``), ascope]
       (* aenv, global scope, arch_frame_list, status *)
       val astate = list_mk_pair [aenv,
				  init_g_scope_list g_scope_ties,
				  arch_frame_list_empty_tm,
				  status_running_tm]
      in
       SOME (actx, astate)
      end
     else raise Fail ("Could not initialise control plane configuration for "^valname)
    end
   else if (is_none arch_opt_tm) then
    (* TODO *)
    NONE
   else raise Fail ("Unknown architecture");
  val _ = case actx_astate_opt of
           SOME (actx, astate) =>
            map (output_hol4_val outstream) (map (fn (a, b, c) => (valname^("_"^a), b, c))
                              (extra_terms@[("actx", actx, actx_of_arch arch_opt_tm), ("astate", astate, astate_of_arch arch_opt_tm)]))
          | NONE => [()];
  val _ = parse_stf outstream stfname_opt valname (pblock_map, fmap, ftymap, blftymap, ttymap_tm) arch_opt_tm
 in
  ()
 end
;

(* Replaces characters to create a valid prefix for HOL4 variable names *)
fun format_for_hol4 (str: string) : string =
    String.translate (fn c => if c = #"-" then "_" else (String.str c)) str;

(* Print test:
 (* OK *)
 val args = ["validation_tests/action_call_table_ebpf.json", "validation_tests/action_call_table_ebpf.log", "mode=concrete_stf"];
 (* OK *)
 val args = ["validation_tests/test_ebpf.json", "validation_tests/test_ebpf.log", "mode=concrete_stf"];

 val args = ["validation_tests/key-bmv2.json", "testlog"];

 val args = ["../../../p4-ipsec/p4/p4/basic.json", "testlog", "mode=symbolic"];

*)

(* The first argument ending in .json starts our arguments; anything before it
 * belongs to buildheap. *)
fun drop_until p [] = []
  | drop_until p (h::t) = if p h then h::t else drop_until p t;

fun opt_value key opts =
 case List.find (String.isPrefix (key^"=")) opts of
   SOME s => SOME (String.extract (s, size key + 1, NONE))
 | NONE => NONE;

(* The architecture is recognised by the package type the program is written against *)
fun detect_arch json_str =
 if String.isSubstring "\"V1Switch\"" json_str then SOME v1model
 else if String.isSubstring "\"ebpfFilter\"" json_str then SOME ebpf
 else if String.isSubstring "\"VSS\"" json_str then SOME vss
 else NONE;

(* Replaces petr4's source-position fields ["info",{...}] by ["missing_info",""],
 * which makes lexing and parsing a lot faster *)
fun strip_info str =
 let
  val marker = "[\"info\","
  fun loop ss acc =
   let
    val (pre, post) = Substring.position marker ss
   in
    if Substring.isEmpty post
    then String.concat (rev ((Substring.string pre)::acc))
    else
     let
      val (_, rest) = Substring.position "]" (Substring.triml (size marker) post)
     in
      loop (Substring.triml 1 rest) ("[\"missing_info\",\"\"]"::(Substring.string pre)::acc)
     end
   end
 in
  loop (Substring.full str) []
 end;

fun ext_map_of_arch arch =
 case arch of
   vss => vss_ext_map
 | ebpf => ebpf_ext_map
 | v1model => v1model_ext_map;

(* Lists the extern calls and constructors in tm that ext_map lacks, by name and arity *)
fun unimplemented_ext_calls ext_map tm =
 let
  fun strip_app l =
   if is_append l
   then let val (l1, l2) = dest_append l in (strip_app l1)@(strip_app l2) end
   else fst $ dest_list l;
  fun arity m = (fromHOLstring $ fst $ dest_pair m, length $ fst $ dest_list $ fst $ dest_pair $ snd $ dest_pair m);
  val arities = map (fn obj => (fromHOLstring $ fst $ dest_pair obj, map arity $ strip_app $ snd $ dest_pair $ snd $ dest_pair obj)) (strip_app ext_map);
  fun is_ext_call t = is_e_call t andalso is_funn_ext (fst $ dest_e_call t);
  fun call_sig t =
   let
    val (funn, args) = dest_e_call t;
    val (obj, meth) = dest_funn_ext funn;
   in
    (fromHOLstring obj, fromHOLstring meth, length $ fst $ dest_list args)
   end;
  fun implemented (obj, meth, n) =
   case List.find (fn (obj', _) => obj' = obj) arities of
     SOME (_, meths) => List.exists (fn (meth', n') => meth' = meth andalso n' = n) meths
   | NONE => false;
  fun sig_to_string (obj, meth, n) =
   (if obj = "" then meth else obj^("."^meth))^(" with "^((Int.toString n)^(if n = 1 then " argument" else " arguments")));
  val ctors = map (fn obj => (fromHOLstring $ fst $ dest_pair obj, is_some $ fst $ dest_pair $ snd $ dest_pair obj)) (strip_app ext_map);
  fun is_inst_call t = is_e_call t andalso is_funn_inst (fst $ dest_e_call t);
  fun constructible obj = List.exists (fn (obj', has_ctor) => obj' = obj andalso has_ctor) ctors;
 in
  (map sig_to_string $ Lib.mk_set $ List.filter (not o implemented) $ map call_sig $ find_terms is_ext_call tm)@
  (map (fn obj => obj^" (constructor)") $ Lib.mk_set $ List.filter (not o constructible) $ map (fromHOLstring o dest_funn_inst o fst o dest_e_call) $ find_terms is_inst_call tm)
 end;

val usage = "Usage: petr4_to_hol4p4 FILE.json LOGFILE [mode=auto|concrete|concrete_stf|symbolic] [arch=vss|ebpf|v1model] [keep-info]\n";

fun main() =
 case drop_until (String.isSuffix ".json") (CommandLine.arguments()) of
   (filename::logname::opts) =>
   let
    val outstream = TextIO.openAppend logname;
    fun fail msg =
     let
      val log_line =
       case excluded_error_desc msg of
         SOME desc => "EXCLUDED: "^(filename^(" requires "^(desc^"\n")))
       | NONE => "FAIL: "^(msg^"\n");
      val _ = TextIO.outputSubstr (outstream, Substring.full log_line);
      val _ = TextIO.closeOut outstream;
      val _ = print (msg^"\n");
     in
      OS.Process.exit (if isSome (excluded_error_desc msg) then OS.Process.success else OS.Process.failure)
     end;

    (* NOTE: This will just remove the suffix .json *)
    val valname_no_suffix = List.drop (rev $ explode filename, 5);
    val stfname = (implode $ rev valname_no_suffix)^".stf";
    val mode =
     case getOpt (opt_value "mode" opts, "auto") of
       "auto" => if OS.FileSys.access (stfname, []) then "concrete_stf" else "concrete"
     | "stf" => "concrete_stf"
     | m => m;
    val _ =
     if mode = "concrete" orelse mode = "concrete_stf" orelse mode = "symbolic"
     then ()
     else fail ("Unknown mode "^(mode^(". "^usage)));
    val stfname_opt = if mode = "concrete_stf" then SOME stfname else NONE;
    val output_extra_maps = (mode = "symbolic");
    val keep_info = List.exists (fn s => s = "keep-info") opts;

    (* TODO: Done in one split instead? *)
    val valname_no_prefix =
     (List.take (valname_no_suffix, Lib.index (fn c => c = #"/") valname_no_suffix))
     handle HOL_ERR _ => valname_no_suffix;
    val valname_prefix =
     (List.drop (valname_no_suffix, Lib.index (fn c => c = #"/") valname_no_suffix))
     handle HOL_ERR _ => [];
    val valname_raw = implode $ rev $ valname_no_prefix;
    val valname = format_for_hol4 valname_raw;
    val prefix = implode $ rev $ valname_prefix;

    val instream = TextIO.openIn filename;
    val json_str = (if keep_info then (fn str => str) else strip_info) (TextIO.inputAll instream);
    val _ = TextIO.closeIn instream;

    val arch_opt =
     case opt_value "arch" opts of
       SOME a =>
       (case parse_arch a of
          SOME arch => SOME arch
        | NONE => fail ("Unknown architecture "^(a^(". "^usage))))
     | NONE =>
       (case detect_arch json_str of
          SOME arch => SOME arch
        | NONE => fail ("Could not detect the architecture of "^(filename^": no V1Switch, ebpfFilter or VSS package found. Use arch=... to override.")));
    val arch_opt_tm = arch_to_term arch_opt;
   in
    case excluded_test_desc valname_raw of
      NONE =>
     let
      val input_tm = stringLib.fromMLstring json_str;
      (* Lexing + parsing to HOL4 JSON *)
      val parse_thm = EVAL ``parse (OUTL (lex (^input_tm) ([]:token list))) [] T``;
      (* TODO: Check if result is INR (OK) or INL (print error) *)
      (* Parsing to HOL4P4 JSON *)
      val parse_clean = EVAL ``p4_from_json ^(rhs $ concl parse_thm) ^(arch_opt_tm)``;
      val final_res_tup = rhs $ concl parse_clean;
     in
      if is_SOME_msg final_res_tup
      then
       let
	val _ =
	 case unimplemented_ext_calls (ext_map_of_arch $ valOf arch_opt) final_res_tup of
	   [] => ()
	 | calls => fail ("Could not parse "^(filename^(". calls of externs that the architecture model does not implement (the extern object counts as an argument): "^(String.concatWith ", " calls))));
	(* TODO: Map this result to everything we need...
	 *       Does not use explicit list to map variable names due to warning *)
	val res_list = pairLib.spine_pair $ dest_SOME_msg final_res_tup;
	(* TODO: Take this as an argument instead *)
	val scriptname = prefix^(valname^"Script.sml");
	val _ =
	 let
	  val outstream = TextIO.openOut scriptname;
	  val _ = output_hol4p4_incipit valname outstream;
(* Debug:
val (ftymap, blftymap) = (el 4 res_list, el 5 res_list)
val fmap = (el 6 res_list)
val pblock_map = (el 10 res_list)
val tbl_entries = (el 11 res_list)
val arch_opt_tm = (el 12 res_list)
val ab_list_tm = (el 13 res_list)
val ttymap_tm = (el 14 res_list)
val pblock_action_names_map_tm = (el 15 res_list)
val oracle_index_tm = (el 16 res_list)
*)
	  val _ = output_hol4p4_vals outstream output_extra_maps valname stfname_opt (el 4 res_list, el 5 res_list) (el 6 res_list) (el 10 res_list) (el 11 res_list) (el 12 res_list) (el 13 res_list) (el 14 res_list) (el 15 res_list) “0:num” (el 16 res_list);
	  val _ = output_hol4p4_explicit outstream;
	 in
	  TextIO.closeOut outstream
	 end
	 handle e =>
	  ((OS.FileSys.remove scriptname handle _ => ());
	   fail ("Could not write the script for "^(filename^(": "^(General.exnMessage e)))));
	val _ = TextIO.outputSubstr (outstream, Substring.full ("OK: Parsed "^(filename^"\n")));
	val _ =
	 if String.isSubstring "\"string\":\"atomic\"},\"body\":" json_str
	 then
	  let
	   val warning = "WARNING: "^(filename^" has @atomic annotations, which the import ignores: the concurrent semantics (conc_red) can interleave the other thread inside them\n");
	  in
	   (TextIO.outputSubstr (outstream, Substring.full warning); print warning)
	  end
	 else ();
	val _ = TextIO.closeOut outstream;
       in
	()
       end
      else
       let
	val parse_error = stringLib.fromHOLstring $ dest_NONE_msg final_res_tup
         handle HOL_ERR _ => "Parsing of JSON was not completed, yielding a incompletely reduced RHS without error message (you might want to check the result of EVAL-ing p4_from_json)";
       in
	fail ("Could not parse "^(filename^(". "^parse_error)))
       end
     end
    | SOME desc =>
     let
      val _ = TextIO.outputSubstr (outstream, Substring.full ("EXCLUDED: "^(filename^" requires "^((desc)^"\n"))));
      val _ = TextIO.closeOut outstream;
     in
      print ""
     end
   end
 | _ => print usage;

val _ = main();

val _ = OS.Process.exit(OS.Process.success);
