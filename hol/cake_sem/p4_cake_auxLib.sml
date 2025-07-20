structure p4_cake_auxLib :> p4_cake_auxLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax bitstringSyntax numSyntax pairSyntax;

open p4Theory;
open p4_cake_auxTheory;
open p4Syntax;

(* Note: This typically sets the word size that strings are serialized to in the CakeML-compilable
 * semantics to either 32 or 64.
 * Also works off the bat for 16 bits, but not 128.
 * Could also be just strings. *)
(* val identifier = “:string”; *)
val identifier = “:word64”;
(* val identifier = “:word32”; *)
(* val identifier = “:word16”; *)

(* This controls whether optimized matching in tables and select will be used *)
val matching_optimization = true;

(* This controls whether optimized I/O (byte instead of bit lists) will be used *)
val io_optimization = false;

(* This should hold all the named strings in core P4, and currently the additional ones for
 * new architectures *)
(* TODO: Move to top level? *)
(* TODO: Can the parts of this belonging to the ext map be generated? *)
val strings =
 ["parseError", "err", "condition", "this", "headerLvalue", "targ1",
  "bits", "data", "b", "b_temp", "standard_metadata", "parsedHdr", "hdr",
  "meta", "check", "checksum", "algo", "size", "result", "index", "value",
  "type", "ingress_port", "egress_spec", "egress_port", "instance_type",
  "packet_length", "enq_timestamp", "enq_qdepth", "deq_timedelta",
  "deq_qdepth", "ingress_global_timestamp", "egress_global_timestamp",
  "mcast_grp", "egress_rid", "checksum_error", "parser_error", "priority",
  "", "accept", "reject", "header", "packet_in", "packet_out",
  "direct_counter", "register", "ipsec_crypt", "isValid", "setValid",
  "setInvalid", "mark_to_drop", "verify", "verify_checksum",
  "update_checksum", "assert", "assume", "extract", "lookahead", "advance",
  "emit", "count", "read", "write", "decrypt_aes_ctr", "encrypt_aes_ctr",
  "encrypt_null", "decrypt_null", "direct_meter", "action_selector",
  "algorithm", "outputWidth", "packet_copy", "inCtrl", "packet",
  "inputPort", "max_index", "CounterArray", "sparse", "increment", "add",
  "headers"];

(* As an SML association list *)
val dict =
 if wordsSyntax.is_word_type identifier
 then
  let
   val width =
    fcpSyntax.dest_int_numeric_type $ wordsSyntax.dest_word_type identifier;
  in
   rev $ foldl (fn (s, l) => ((s, wordsSyntax.mk_wordii (length l, width))::l)) [] strings
  end
 else if identifier = “:string”
 then
  foldr (fn (s, l) => ((s, stringSyntax.fromMLstring s)::l)) [] strings
 else raise raise (mk_HOL_ERR "p4_cake_auxLib" "dict" ("identifier type not supported:"^(type_to_string identifier)));

(* As a Redblackmap dict *)
val cake_dict = Redblackmap.fromList String.compare dict;

(* As a term *)
val cake_dict_tm = mk_list (map (fn (a,b) => mk_pair (stringSyntax.fromMLstring a, b)) $ Redblackmap.listItems cake_dict, “:(string # ^identifier)”);

fun get_id name =
 let
  val entry = Redblackmap.peek (cake_dict, name)
 in
  if isSome entry
  then 
   valOf entry
  else raise (mk_HOL_ERR "p4_cake_auxLib" "get_id" ("key not found in cake_dict: "^name))
 end
;

(* Some extra tricks for CakeML export *)

fun to_fixwidth_n2v_CONV tm =
 let
  val elems = fst $ dest_list tm
  val len = length elems
  val n = rhs $ concl $ EVAL $ mk_v2n $ mk_list (elems, bool)
  val rewrite = GSYM $ EVAL $ mk_fixwidth (term_of_int len, mk_n2v n)
 in
  REWRITE_CONV [rewrite] tm
 end
;

(* This simpset fragment takes bool lists and converts them to a less verbose format
 * involving fewer constants *)
val BOOL_LIST_ss =
 SSFRAG {name = SOME "BOOL_LIST_ss",
	 convs = [{conv = K $ K to_fixwidth_n2v_CONV,
		   key= SOME ([], mk_var ("bool_list", mk_list_type bool)),
		   name = "to_fixwidth_n2v_CONV",
		   trace = 2}],
	 rewrs = [],
         ac = [],
	 filter = NONE,
	 dprocs = [],
	 congs = []
 };

val (word_tm, mk_word, dest_word, is_word) =
  syntax_fns2 "p4_aux" "word";

fun to_word_CONV tm =
 let
  val (list, width) = dest_pair tm
  val elems = fst $ dest_list list
  (* TODO: Check agreement *)
  val n = rhs $ concl $ EVAL $ mk_v2n $ mk_list (elems, bool)
  val rewrite = GSYM $ EVAL $ mk_word (n, width)
 in
  REWRITE_CONV [rewrite] tm
 end
;

val BOOL_LIST_ss' =
 SSFRAG {name = SOME "BOOL_LIST_ss'",
	 convs = [{conv = K $ K to_word_CONV,
		   key= SOME ([], mk_pair (mk_var ("bool_list", mk_list_type bool), mk_var ("width", num))),
		   name = "to_word_CONV",
		   trace = 2}],
	 rewrs = [],
         ac = [],
	 filter = NONE,
	 dprocs = [],
	 congs = []
 };


(******************)
(* Creating input *)

val (tau_in_bit_rand_tm, mk_tau_in_bit_rand, dest_tau_in_bit_rand, is_tau_in_bit_rand) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_rand";
val (tau_in_bit_fix_tm, mk_tau_in_bit_fix, dest_tau_in_bit_fix, is_tau_in_bit_fix) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_fix";

fun n_coin_flips 0 = []
  | n_coin_flips n =
   mlibUseful.coin_flip () :: (n_coin_flips (n-1))
;

fun bitstring_of_tau_in_list' [] = “[]:bool list”
  | bitstring_of_tau_in_list' (h::t) =
   if is_tau_in_bit_rand h
   then
    let
     val width = int_of_term $ dest_tau_in_bit_rand h
    in
     mk_append (mk_list (map (lift_bool bool) $ n_coin_flips width, bool),  bitstring_of_tau_in_list' t)
    end
   else if is_tau_in_bit_fix h
   then
    let
     val (value, width) = dest_pair $ dest_tau_in_bit_fix h
     val bitlist_tm = rhs $ concl $ EVAL “fixwidth ^width $ n2v ^value”
    in
     mk_append (bitlist_tm,  bitstring_of_tau_in_list' t)
    end
   else raise Fail "Subtype not supported"
;
fun bitstring_of_tau_in_list l =
 rhs $ concl $ EVAL $ bitstring_of_tau_in_list' (fst $ dest_list l)
;

val (tau_in_bit_fix_tm, mk_tau_in_bit_fix, dest_tau_in_bit_fix, is_tau_in_bit_fix) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_fix";

val (acc_fld_tm, mk_acc_fld, dest_acc_fld, is_acc_fld) =
  syntax_fns1 "p4_cake_aux" "acc_fld";
val (acc_struct_tm, mk_acc_struct, dest_acc_struct, is_acc_struct) =
  syntax_fns2 "p4_cake_aux" "acc_struct";

fun mk_acc []      = raise Fail "Can't make a field access with no string names"
  | mk_acc (h::[]) = mk_acc_fld (stringLib.fromMLstring h)
  | mk_acc (h::t)  = mk_acc_struct (stringLib.fromMLstring h, mk_acc t)
;

fun update_entries [] tau_in = tau_in
  | update_entries ((acc, new_val)::t) tau_in =
 let
  val acc_tm = mk_acc $ mlibUseful.split "." acc
  val tau_in' = optionSyntax.dest_some $ rhs $ concl $ EVAL “update_tau_in ^acc_tm ^(term_of_int new_val) ^tau_in”
 in
  update_entries t tau_in'
 end
;

(* TODO: This simply generates an input packet based on the shape of the "H" type parameter in V1Model,
 * and names of sub-structs and fields *)
fun v1model_get_input actx fixed_fields components =
 let
  val input_f_tm = #4 $ dest_actx actx
  val hdr_tm = fst $ dest_pair $ snd $ dest_comb input_f_tm
  val tau_in = rhs $ concl $ EVAL “tau_to_tau_in $ THE $ tau_of_type $ type_of_v ^hdr_tm”
(* Length check:
val tau_in_sum = rhs $ concl $ EVAL “tau_in_sum ^tau_in”
*)
  val tau_in' = update_entries fixed_fields tau_in
  val tau_in'' = rhs $ concl $ EVAL “filter_tau_in ^tau_in' ^(mk_list (map stringLib.fromMLstring components, stringLib.string_ty))”
  val tau_in_list = rhs $ concl $ EVAL “tau_in_to_list ^tau_in''”
(* Length checks:
val tau_in_sum = rhs $ concl $ EVAL “tau_in_sum ^tau_in'”
val tau_in_sum = rhs $ concl $ EVAL “FOLDL (\a b. (a:num) + (b:num) ) 0 $ MAP tau_in_sum ^tau_in_list”
*)
 in
  bitstring_of_tau_in_list tau_in_list
 end
;

fun invert_dict dict =
 rhs $ concl $ EVAL “invert_dict ^dict”
;

local
fun deparse_bool_list' l =
   case l of
     [] => []
   | h::t =>
    if Teq h
    then (#"1"::(deparse_bool_list' t))
    else (#"0"::(deparse_bool_list' t))
 ;
in
fun deparse_bool_list l =
 implode $ deparse_bool_list' $ fst $ listSyntax.dest_list l
end

exception ParseError of string;

local
fun parse_bool_list' l =
      case l of
	[] => []
      | h::t =>
       if h = #"0"
       then (F::(parse_bool_list' t))
       else if h = #"1"
       then (T::(parse_bool_list' t))
       else raise ParseError ("Error: packet should be specified using only 0s and 1s to signify bits.\n")
    ;
in
fun parse_bool_list l =
 listSyntax.mk_list (parse_bool_list' $ String.explode l, bool);
end

(* Converts a SML hex string into a HOL4 list of Booleans *)
fun hex_to_bool_list hex_string =
 let
  val hex_string_no_spaces = String.implode (List.filter (fn c => c <> #" " andalso c <> #".") (String.explode hex_string));
  val len = term_of_int $ (size hex_string_no_spaces) * 4;
  val hex_string_no_spaces_tm = stringLib.fromMLstring hex_string_no_spaces
  val num_tm = optionSyntax.dest_some $ rhs $ concl $ EVAL “fromHexString ^hex_string_no_spaces_tm”
  val bin_string_tm = rhs $ concl $ EVAL “num_to_bin_string ^num_tm”
  val n_leading_zeroes = rhs $ concl $ EVAL “^len - (LENGTH ^bin_string_tm)”
  val bin_string_padded_tm = rhs $ concl $ EVAL “(IMPLODE $ REPLICATE ^n_leading_zeroes #"0") ++ ^bin_string_tm”
  val bool_list_tm = parse_bool_list $ stringLib.fromHOLstring bin_string_padded_tm;
 in
  bool_list_tm
 end
;

fun bool_list_to_hex bool_list =
 let
  val bin_str = deparse_bool_list bool_list;

  fun bin_to_hex bin_str =
    let
      fun nybble_to_hex nybble =
        case nybble of
            "0000" => "0"
          | "0001" => "1"
          | "0010" => "2"
          | "0011" => "3"
          | "0100" => "4"
          | "0101" => "5"
          | "0110" => "6"
          | "0111" => "7"
          | "1000" => "8"
          | "1001" => "9"
          | "1010" => "A"
          | "1011" => "B"
          | "1100" => "C"
          | "1101" => "D"
          | "1110" => "E"
          | "1111" => "F"
          | _ => raise Fail ("Invalid nybble: " ^ nybble)

      fun process_nybbles (str, acc, i:int, hex_count:int) =
        if i >= String.size str then
          acc
        else
          let
            val nybble = String.substring(str, i, 4)
            val hex_digit = nybble_to_hex nybble
            (* Add a space after every second hex digit, except for the last one *)
            val acc' = acc ^ hex_digit ^ 
                        (if (hex_count + 1) mod 2 = 0 andalso i + 4 < String.size str 
                         then " " else "")
          in
            process_nybbles (str, acc', i + 4, hex_count + 1)
          end
    in
      if String.size bin_str mod 8 <> 0 then
        raise Fail "Binary string length must be divisible by 8"
      else
        process_nybbles (bin_str, "", 0, 0)
    end
  ;

 in
  bin_to_hex bin_str
 end
;

fun get_keys [] = []
  | get_keys (h::t) =
 let
  val matching = fst $ dest_pair h
  val (s_list_tm, prio) = dest_pair matching
  val s_list = fst $ dest_list $ s_list_tm
 in
  if length s_list = 1
  then
   let
    val s = el 1 s_list
   in
    if is_s_sing s
    then
     let
      val (bool_list_tm, width_tm) = dest_pair $ dest_v_bit $ dest_s_sing s
      val value = int_of_term $ rhs $ concl $ EVAL “v2n ^bool_list_tm”
      val width = int_of_term width_tm
     in
      ((value, width), int_of_term prio)::(get_keys t)
     end
    else raise Fail "get_keys only supports s_sing"
   end
  else raise Fail "get_keys only supports single matching keys (got multiple entries)"
 end
;

(* Populate a table with singleton keys, outside of existing entries.
 * Used for creating dummy entries for benchmarking table matching *)
(* TODO: How to best handle priority? Best make new entries the prioritized ones... *)
fun populate_table tbl rand_gen n_additional_entries =
 let
  val (name, entries) = dest_pair tbl
  val entries_list_tm = p4_coreLib.dest_tbl_regular entries
  val entries_list = fst $ dest_list $ entries_list_tm
  val (keys, prios) = unzip $ get_keys entries_list
  (* TODO: Hack. Warn if widths disagree. *)
  val width = el 1 $ map snd keys

  val max_prio = fst $ mlibUseful.max (fn (a,b) => Int.compare (a, b)) prios

  (* TODO: Re-do randomization for doubles? *)
  fun add_entries existing_keys width rand_gen 0 = []
    | add_entries existing_keys width rand_gen n_additional_entries =
   let
    val new_entry = Random.range (0, (funpow width (fn a => a*2) 1)) rand_gen;
    val new_entry' = mk_s_sing $ rhs $ concl $ EVAL $ mk_v_bitii (new_entry, width)
   in
    if not $ exists (fn a => a = new_entry) existing_keys
    then new_entry'::(add_entries existing_keys width rand_gen (n_additional_entries-1))
    else (add_entries existing_keys width rand_gen (n_additional_entries-1))
   end
  ;

  (* TODO: Take action as an argument *)
  val action =
   “("NoAction",
      [e_v (v_bool T); e_v (v_bool T)])”
  val new_entries = add_entries (map fst keys) width rand_gen n_additional_entries
  val new_entries' = map (fn a => mk_pair (mk_list ([a], “:s”), term_of_int (max_prio+1))) new_entries
  val new_entries_tm = mk_list (map (fn a => mk_pair (a, action)) new_entries', “:(s list # num) # string # e list”)

  val entries_list_tm' = rhs $ concl $ EVAL “^new_entries_tm ++ ^entries_list_tm”
  
 in
  mk_pair (name, p4_coreLib.mk_tbl_regular entries_list_tm')
 end
;

end
