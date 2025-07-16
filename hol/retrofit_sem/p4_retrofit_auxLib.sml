structure p4_retrofit_auxLib :> p4_retrofit_auxLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax bitstringSyntax numSyntax pairSyntax;

open p4Theory;
open p4Syntax;

(* Note: This typically sets the word size that strings are serialized to in the CakeML-compilable
 * semantics to either 32 or 64.
 * Also works off the bat for 16 bits, but not 128.
 * Could also be just strings. *)
val identifier = “:string”;
(* val identifier = “:word64”; *)
(* val identifier = “:word32”; *)
(* val identifier = “:word16”; *)

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
 else raise raise (mk_HOL_ERR "p4_retrofit_auxLib" "dict" ("identifier type not supported:"^(type_to_string identifier)));

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
  else raise (mk_HOL_ERR "p4_retrofit_auxLib" "get_id" ("key not found in cake_dict: "^name))
 end
;

end
