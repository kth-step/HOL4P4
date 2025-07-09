structure p4_cake_auxLib :> p4_cake_auxLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax bitstringSyntax numSyntax pairSyntax;

open p4Theory;
open p4_cake_auxTheory;
open p4Syntax;

(* Note: This typically sets the word size that strings are serialized to in the CakeML-compilable
 * semantics to either 32 or 64. Could also be just strings. *)
(* val identifier = “:string”; *)
val identifier = “:word64”;
(* val identifier = “:word32”; *)

(* TODO: Can parts of this belonging to the ext map be generated? *)
val cake_dict = Redblackmap.fromList String.compare 
  [("parseError", (“"parseError"”, “0w:word64”, “0w:word32”)),
   ("err", (“"err"”, “1w:word64”, “1w:word32”)),
   ("condition", (“"condition"”, “2w:word64”, “2w:word32”)),
   ("this", (“"this"”, “3w:word64”, “3w:word32”)),
   ("headerLvalue", (“"headerLvalue"”, “4w:word64”, “4w:word32”)),
   ("targ1", (“"targ1"”, “5w:word64”, “5w:word32”)),
   ("bits", (“"bits"”, “6w:word64”, “6w:word32”)),
   ("data", (“"data"”, “7w:word64”, “7w:word32”)),
   ("b", (“"b"”, “8w:word64”, “8w:word32”)),
   ("b_temp", (“"b_temp"”, “9w:word64”, “9w:word32”)),
   ("standard_metadata", (“"standard_metadata"”, “10w:word64”, “10w:word32”)),
   ("parsedHdr", (“"parsedHdr"”, “11w:word64”, “11w:word32”)),
   ("hdr", (“"hdr"”, “12w:word64”, “12w:word32”)),
   ("meta", (“"meta"”, “13w:word64”, “13w:word32”)),
   ("check", (“"check"”, “14w:word64”, “14w:word32”)),
   ("checksum", (“"checksum"”, “15w:word64”, “15w:word32”)),
   ("algo", (“"algo"”, “16w:word64”, “16w:word32”)),
   ("size", (“"size"”, “17w:word64”, “17w:word32”)),
   ("result", (“"result"”, “18w:word64”, “18w:word32”)),
   ("index", (“"index"”, “19w:word64”, “19w:word32”)),
   ("value", (“"value"”, “20w:word64”, “20w:word32”)),
   ("type", (“"type"”, “21w:word64”, “21w:word32”)),
   ("ingress_port", (“"ingress_port"”, “22w:word64”, “22w:word32”)),
   ("egress_spec", (“"egress_spec"”, “23w:word64”, “23w:word32”)),
   ("egress_port", (“"egress_port"”, “24w:word64”, “24w:word32”)),
   ("instance_type", (“"instance_type"”, “25w:word64”, “25w:word32”)),
   ("packet_length", (“"packet_length"”, “26w:word64”, “26w:word32”)),
   ("enq_timestamp", (“"enq_timestamp"”, “27w:word64”, “27w:word32”)),
   ("enq_qdepth", (“"enq_qdepth"”, “28w:word64”, “28w:word32”)),
   ("deq_timedelta", (“"deq_timedelta"”, “29w:word64”, “29w:word32”)),
   ("deq_qdepth", (“"deq_qdepth"”, “30w:word64”, “30w:word32”)),
   ("ingress_global_timestamp", (“"ingress_global_timestamp"”, “31w:word64”, “31w:word32”)),
   ("egress_global_timestamp", (“"egress_global_timestamp"”, “32w:word64”, “32w:word32”)),
   ("mcast_grp", (“"mcast_grp"”, “33w:word64”, “33w:word32”)),
   ("egress_rid", (“"egress_rid"”, “34w:word64”, “34w:word32”)),
   ("checksum_error", (“"checksum_error"”, “35w:word64”, “35w:word32”)),
   ("parser_error", (“"parser_error"”, “36w:word64”, “36w:word32”)),
   ("priority", (“"priority"”, “37w:word64”, “37w:word32”)),
   ("", (“""”, “38w:word64”, “38w:word32”)),
   ("accept", (“"accept"”, “39w:word64”, “39w:word32”)),
   ("reject", (“"reject"”, “40w:word64”, “40w:word32”)),
   ("header", (“"header"”, “41w:word64”, “41w:word32”)),
   ("packet_in", (“"packet_in"”, “42w:word64”, “42w:word32”)),
   ("packet_out", (“"packet_out"”, “43w:word64”, “43w:word32”)),
   ("direct_counter", (“"direct_counter"”, “44w:word64”, “44w:word32”)),
   ("register", (“"register"”, “45w:word64”, “45w:word32”)),
   ("ipsec_crypt", (“"ipsec_crypt"”, “46w:word64”, “46w:word32”)),
   ("isValid", (“"isValid"”, “47w:word64”, “47w:word32”)),
   ("setValid", (“"setValid"”, “48w:word64”, “48w:word32”)),
   ("setInvalid", (“"setInvalid"”, “49w:word64”, “49w:word32”)),
   ("mark_to_drop", (“"mark_to_drop"”, “50w:word64”, “50w:word32”)),
   ("verify", (“"verify"”, “51w:word64”, “51w:word32”)),
   ("verify_checksum", (“"verify_checksum"”, “52w:word64”, “52w:word32”)),
   ("update_checksum", (“"update_checksum"”, “53w:word64”, “53w:word32”)),
   ("assert", (“"assert"”, “54w:word64”, “54w:word32”)),
   ("assume", (“"assume"”, “55w:word64”, “55w:word32”)),
   ("extract", (“"extract"”, “56w:word64”, “56w:word32”)),
   ("lookahead", (“"lookahead"”, “57w:word64”, “57w:word32”)),
   ("advance", (“"advance"”, “58w:word64”, “58w:word32”)),
   ("emit", (“"emit"”, “59w:word64”, “59w:word32”)),
   ("count", (“"count"”, “60w:word64”, “60w:word32”)),
   ("read", (“"read"”, “61w:word64”, “61w:word32”)),
   ("write", (“"write"”, “62w:word64”, “62w:word32”)),
   ("decrypt_aes_ctr", (“"decrypt_aes_ctr"”, “63w:word64”, “63w:word32”)),
   ("encrypt_aes_ctr", (“"encrypt_aes_ctr"”, “64w:word64”, “64w:word32”)),
   ("encrypt_null", (“"encrypt_null"”, “65w:word64”, “65w:word32”)),
   ("decrypt_null", (“"decrypt_null"”, “66w:word64”, “66w:word32”)),
   ("direct_meter", (“"direct_meter"”, “67w:word64”, “67w:word32”)),
   ("action_selector", (“"action_selector"”, “68w:word64”, “68w:word32”)),
   ("algorithm", (“"algorithm"”, “69w:word64”, “69w:word32”)),
   ("outputWidth", (“"outputWidth"”, “70w:word64”, “70w:word32”)),
   ("packet_copy", (“"packet_copy"”, “71w:word64”, “71w:word32”)),
   ("inCtrl", (“"inCtrl"”, “72w:word64”, “72w:word32”)),
   ("packet", (“"packet"”, “73w:word64”, “73w:word32”)),
   ("inputPort", (“"inputPort"”, “74w:word64”, “74w:word32”)),
   ("max_index", (“"max_index"”, “75w:word64”, “75w:word32”)),
   ("CounterArray", (“"CounterArray"”, “76w:word64”, “76w:word32”)),
   ("sparse", (“"sparse"”, “77w:word64”, “77w:word32”)),
   ("increment", (“"increment"”, “78w:word64”, “78w:word32”)),
   ("add", (“"add"”, “79w:word64”, “79w:word32”)),
   ("headers", (“"headers"”, “80w:word64”, “80w:word32”))];

val get_element =
 if identifier = “:string”
 then (fn (a:term,b:term,c:term) => a)
 else if identifier = “:word64”
 then (fn (a,b,c) => b)
 else if identifier = “:word32”
 then (fn (a,b,c) => c)
 else raise (mk_HOL_ERR "p4_cake_auxLib" "get_dict" ("identifier type not supported:"^(type_to_string identifier)))
;

val cake_dict_tm = mk_list(map (fn (a,b) => mk_pair (stringSyntax.fromMLstring a, get_element b)) $ Redblackmap.listItems cake_dict, “:(string # ^identifier)”);

fun get_id name =
 let
  val entry = Redblackmap.peek (cake_dict, name)
 in
  if isSome entry
  then 
   if identifier = “:string”
   then #1 $ valOf entry
   else if identifier = “:word64”
   then #2 $ valOf entry
   else if identifier = “:word32”
   then #3 $ valOf entry
   else raise (mk_HOL_ERR "p4_cake_auxLib" "get_id" ("identifier type not supported:"^(type_to_string identifier)))
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

(* TODO: Make syntax file *)
val (match_all_e_alt_tm, mk_match_all_e_alt, dest_match_all_e_alt, is_match_all_e_alt) =
  syntax_fns2 "p4_aux" "match_all_e_alt";

fun get_keys [] = []
  | get_keys (h::t) =
 let
  val match_fun = fst $ dest_pair h
  val (f, prio) = dest_pair match_fun
  val s_list = fst $ dest_list $ snd $ dest_comb f
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
  val entries_list = fst $ dest_list entries
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
  val new_entries' = map (fn a => mk_pair (mk_comb (match_all_e_alt_tm, mk_list ([a], “:s”)), term_of_int (max_prio+1))) new_entries
  val new_entries_tm = mk_list (map (fn a => mk_pair (a, action)) new_entries', “:((e list -> bool) # num) # string # e list”)
  
 in
  mk_pair (name, rhs $ concl $ EVAL “^new_entries_tm ++ (SND ^tbl)”)
 end
;

end
