structure p4_cake_transformLib = struct

open HolKernel boolLib Parse bossLib;

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

open p4_arch_cakeTheory;
open p4_cake_transformTheory;

open listSyntax optionSyntax pairSyntax;

(* TODO: Clean up the below, put in a separate library that's compiled before p4_v1modelTheory *)

(* Generating string-to-word64 dictionary:

(* Gather extern function implementations, which may contain hard-coded variable names *)
val core_implementations =
 [verify_gen_def, header_is_valid_def, header_set_valid_def, header_set_invalid_def,
  packet_in_extract_gen_def, packet_in_lookahead_gen_def, packet_in_advance_gen_def,
  packet_out_emit_gen_def]

(* Filter out identical terms while keeping their order *)
local
 fun filter_equal_terms' []     filtered_list = filtered_list
  | filter_equal_terms' (h::t) [] = filter_equal_terms' t [h]
  | filter_equal_terms' (h::t) filtered_list =
   if isSome (List.find (term_eq h) filtered_list)
   then filter_equal_terms' t filtered_list
   else filter_equal_terms' t (h::filtered_list)
in
fun filter_equal_terms tm_list = rev $ filter_equal_terms' tm_list []
end
;

fun get_varn_name_strings impls =
 let
  val impl_tms = map (rhs o snd o strip_forall o concl) impls
  val varn_names = foldl (fn (tm, l) => l@(find_terms (fn t => is_varn_name t) tm)) [] impl_tms
 in
  map dest_varn_name $ filter_equal_terms varn_names
 end
;

fun get_ext_map_strings ext_map =
 let
  val ext_map_list = fst $ dest_list ext_map
  val (ext_obj_names, ext_objs) = unzip $ map dest_pair ext_map_list
  val ext_obj_func_maps = map (fst o dest_list) $ map (snd o dest_pair) ext_objs
  val ext_func_names = flatten $ map (map (fst o dest_pair)) $ ext_obj_func_maps
 in
  ext_obj_names@ext_func_names
 end
;

(* Note: parseError hard-coded *)
val core_impl_varnames = (“"parseError"”)::(get_varn_name_strings core_implementations)

local
fun add_to_dict' []     dict _     = dict
  | add_to_dict' (h::t) dict i =
 let
  val word = wordsSyntax.mk_wordii (i, 64)
 in
    case Redblackmap.peek (dict, h) of
     SOME v => add_to_dict' t dict i
   | NONE => add_to_dict' t (Redblackmap.insert (dict, h, word)) (i+1)
 end  
in
fun add_to_dict additions dict =
 let
  val size = Redblackmap.numItems dict
 in
  add_to_dict' additions dict size
 end
end

val varnames_of_vmap = map (fst o pairSyntax.dest_pair) o (fst o listSyntax.dest_list)

val core_impl_dict =
 add_to_dict core_impl_varnames (Redblackmap.mkDict (fn (a,b) => String.compare (stringSyntax.fromHOLstring a, stringSyntax.fromHOLstring b))):(term, term) Redblackmap.dict;

val items = Redblackmap.listItems core_impl_dict

local
val n_of_w:term * term -> int = wordsSyntax.uint_of_word o snd
in
fun sort_alist list =
 mlibUseful.sort (fn (a,b) => Int.compare (n_of_w a, n_of_w b)) list
end

(* Translation of core variable names, can this easily be done automatically somehow,
 * without changing the core semantics? *)

val alist_tm = listSyntax.mk_list (map mk_pair $ sort_alist items, mk_prod (“:string”, “:word64”))

[(“"parseError"”, “0w”),
 (“"err"”, “1w”),
 (“"condition"”, “2w”),
 (“"this"”, “3w”),
 (“"headerLvalue"”, “4w”),
 (“"targ1"”, “5w”)
 (“"bits"”, “6w”),
 (“"data"”, “7w”)]

*)


(*

val dict = [(“"parseError"”, “0w:word64”), (“"err"”, “1w:word64”), (“"condition"”, “2w:word64”),
 (“"this"”, “3w:word64”), (“"headerLvalue"”, “4w:word64”), (“"targ1"”, “5w:word64”),
 (“"bits"”, “6w:word64”), (“"data"”, “7w:word64”), (“"b"”, “8w:word64”), (“"b_temp"”, “9w:word64”),
 (“"standard_metadata"”, “10w:word64”), (“"parsedHdr"”, “11w:word64”), (“"hdr"”, “12w:word64”),
 (“"meta"”, “13w:word64”), (“"check"”, “14w:word64”), (“"checksum"”, “15w:word64”),
 (“"algo"”, “16w:word64”), (“"size"”, “17w:word64”), (“"result"”, “18w:word64”),
 (“"index"”, “19w:word64”), (“"value"”, “20w:word64”)];

val dict_tm = listSyntax.mk_list (map mk_pair dict, mk_prod (“:string”, “:word64”))

*)

(*
(* Some specific stuff left out for now *)
val v1model_implementations =
 [v1model_mark_to_drop_def, v1model_assert_def, v1model_assume_def,
  v1model_direct_counter_construct_def, v1model_direct_counter_count_def,
  v1model_verify_checksum_def, v1model_update_checksum_def, register_construct_def,
  register_read_def, register_write_def]

(* Architectural functions mentioning variables by hard-coded names *)
val v1model_archfuns = [v1model_postparser_def]

(* "type" added manually - it's an argument to direct counter constructor, but not used *)
val v1model_varnames = (get_varn_name_strings (v1model_implementations@v1model_archfuns))@[“"type"”]

val v1model_init_vmapnames = varnames_of_vmap p4_v1modelLib.v1model_init_v_map

(* TODO: just copy-pasted from V1Model Script file, put in V1Model Lib *)
val v_map_varnames =
 [“"b"”, “"b_temp"”, “"standard_metadata"”, “"parsedHdr"”, “"hdr"”, “"meta"”]
;

(* The field names from standard_metadata *)
val v_map_fieldnames = map (fst o pairSyntax.dest_pair) $ fst $ listSyntax.dest_list p4_v1modelLib.v1model_standard_metadata_zeroed_tm

val v1model_parser_state_names = [“""”, “"accept"”, “"reject"”]

(* TODO: Add all object and method names from ext_map *)
val v1model_ext_map_strings = get_ext_map_strings $ rhs $ concl $ EVAL p4_v1modelLib.v1model_ext_map

val v1model_dict =
 add_to_dict (v1model_init_vmapnames@v_map_varnames@v1model_varnames@v_map_fieldnames@v1model_parser_state_names@v1model_ext_map_strings) core_impl_dict;

val v1model_items = Redblackmap.listItems v1model_dict

val n_of_w:term * term -> int = wordsSyntax.uint_of_word o snd

val v1model_items_sorted = mlibUseful.sort (fn (a,b) => Int.compare (n_of_w a, n_of_w b)) v1model_items

val v1model_dict = listSyntax.mk_list (map mk_pair v1model_items_sorted, mk_prod (“:string”, “:word64”))

*)

(* TODO: The latter part of this belonging to the ext map may be generated... *)
val v1model_dict =
   “[("parseError",0w); ("err",1w); ("condition",2w); ("this",3w);
     ("headerLvalue",4w); ("targ1",5w); ("bits",6w); ("data",7w); ("b",8w);
     ("b_temp",9w); ("standard_metadata",10w); ("parsedHdr",11w);
     ("hdr",12w); ("meta",13w); ("check",14w); ("checksum",15w);
     ("algo",16w); ("size",17w); ("result",18w); ("index",19w);
     ("value",20w); ("type",21w); ("ingress_port",22w); ("egress_spec",23w);
     ("egress_port",24w); ("instance_type",25w); ("packet_length",26w);
     ("enq_timestamp",27w); ("enq_qdepth",28w); ("deq_timedelta",29w);
     ("deq_qdepth",30w); ("ingress_global_timestamp",31w);
     ("egress_global_timestamp",32w); ("mcast_grp",33w); ("egress_rid",34w);
     ("checksum_error",35w); ("parser_error",36w); ("priority",37w);
     ("",38w); ("accept",39w); ("reject",40w); ("header",41w);
     ("packet_in",42w); ("packet_out",43w); ("direct_counter",44w);
     ("register",45w); ("ipsec_crypt",46w); ("isValid",47w);
     ("setValid",48w); ("setInvalid",49w); ("mark_to_drop",50w);
     ("verify",51w); ("verify_checksum",52w); ("update_checksum",53w);
     ("assert",54w); ("assume",55w); ("extract",56w); ("lookahead",57w);
     ("advance",58w); ("emit",59w); ("count",60w); ("read",61w);
     ("write",62w); ("decrypt_aes_ctr",63w); ("encrypt_aes_ctr",64w);
     ("encrypt_null",65w); ("decrypt_null",66w)]:(string, word64) alist”;

(* Uses a dict of static, architecture-coded variable names. add_varnames_actx will pick
 * up the rest. Returns a tuple of a new dict and the actx'. *)
fun transform_actx dict actx =
 let
  val dict' = rhs $ concl $ EVAL “add_varnames_actx ^dict ^actx”
  val (_, _, _, input_f, _, _, _, apply_table_f, _, _) = dest_actx actx
  val (param1, param2) = dest_pair $ snd $ dest_comb input_f
  (* TODO: Smart error handling *)
  val dict'' = rhs $ concl $ computeLib.RESTR_EVAL_CONV [“word”] “add_varnames_v ^dict' ^param1”
  val dict''' = rhs $ concl $ computeLib.RESTR_EVAL_CONV [“word”] “add_varnames_v ^dict'' ^param2”

  val param1' = dest_some $ rhs $ concl $ computeLib.RESTR_EVAL_CONV [“word”] “transform_v ^dict''' ^param1”
  val param2' = dest_some $ rhs $ concl $ computeLib.RESTR_EVAL_CONV [“word”] “transform_v ^dict''' ^param2”

  val input_f' = mk_comb (“v1model_input_f'”, mk_pair (param1', param2'))
  val actx'_opt = rhs $ concl $ computeLib.RESTR_EVAL_CONV [“word”] “transform_actx ^dict''' ^actx”

 in
  if is_some actx'_opt
  then
   let
    val [ab_list', pblock_map', ext_map', func_map'] = strip_pair $ dest_some actx'_opt
    val postparser_w = dest_some $ rhs $ concl $ EVAL “ALOOKUP ^dict''' "postparser"”
   in
    (dict', list_mk_pair [“^ab_list':ab_list'”, “^pblock_map':pblock_map'”, “[(^postparser_w,ffblock_ff v1model_postparser')]:v1model_ascope' ffblock_map'”, “(^input_f'):v1model_ascope' input_f'”, “v1model_output_f':v1model_ascope' output_f'”, “v1model_copyin_pbl':v1model_ascope' copyin_pbl'”, “v1model_copyout_pbl':v1model_ascope' copyout_pbl'”, “v1model_apply_table_f':v1model_ascope' apply_table_f'”, “^ext_map':v1model_ascope' ext_map'”, “^func_map':func_map'”])
   end
  else raise Fail "transform_actx failed to translate actx"
 end
;

fun transform_match_fun dict match_fun =
 let
  val (f, prio) = dest_pair match_fun
  val (t1, t2) = dest_abs f
  val t_name = fst $ dest_var t1
  val t1' = mk_var (t_name, “:e' list”)
  val (match_all, t3) = dest_comb t2
  val (zip, t4) = dest_comb t3
  val (map_tm, s_list) = dest_pair t4
  val map_tm' = “MAP v'_of_e' ^t1'”;
  val s'_list_opt = rhs $ concl $ EVAL “oFOLDR (transform_s ^dict) ^s_list”
 in
  if is_some s'_list_opt
  then mk_pair (mk_abs (t1', mk_comb (“match_all'”, mk_zip (map_tm', dest_some s'_list_opt))), prio)
  else raise Fail "transform_match_fun failed to translate set expression list"
 end
;

fun transform_entries dict [] = []
  | transform_entries dict (h::t) =
 let
  val (match_fun, action) = dest_pair h
  val (name, args) = dest_pair action
  val name'_opt = rhs $ concl $ EVAL “ALOOKUP ^dict ^name”
 in
  if is_some name'_opt
  then
   let
    val name' = dest_some name'_opt
    val argsl'_opt = rhs $ concl $ EVAL “transform_e ^dict (e_list ^args)”
   in
    if is_some argsl'_opt
    then
     let
      (* TODO: hack, make syntax function *)
      val args' = snd $ dest_comb $ dest_some argsl'_opt
      val res = transform_entries dict t
     in
      ((mk_pair (transform_match_fun dict match_fun, mk_pair (name', args')) )::res)
     end
    else raise Fail "transform_entries failed to translate action arguments"
   end
  else raise Fail "transform_entries failed to translate action name (one or more action names could not be found in the dictionary)"
 end
;

fun transform_tbl dict tbl =
 let
  val (name, entries) = dest_pair tbl
  val name'_opt = rhs $ concl $ EVAL “ALOOKUP ^dict ^name”
 in
  if is_some name'_opt
  then
   let
    val entries' = transform_entries dict (fst $ dest_list entries)
   in
    mk_pair (dest_some name'_opt, mk_list (entries', “:((e' list -> bool) # num) # word64 # e' list”))
   end
  else raise Fail "transform_tbl failed to translate table name (one or more table names could not be found in the dictionary)"
 end
;
fun transform_ctrl dict ctrl =
 mk_list (map (transform_tbl dict) (fst $ dest_list ctrl), “:word64 # (((e' list -> bool) # num) # word64 # e' list) list”)
;

(* TODO: Updated ctrl as argument, for now... *)
(*
val dict = v1model_dict;
val ctrl' = “[]:v1model_ctrl'”;
*)
fun transform_program dict actx astate =
 let
  val (dict', actx') = transform_actx dict actx
  val ctrl = #4 $ p4_testLib.dest_ascope $ #4 $ dest_aenv $ #1 $ dest_astate astate;
  (* TODO: Note that ctrl has to be translated in SML due to the matching function, which cannot be
   * be syntactically treated in HOL4 *)
  val ctrl' = transform_ctrl dict' ctrl
  val astate'_opt = rhs $ concl $ EVAL “transform_astate ^dict' ^astate ^ctrl'”
 in
  if is_some astate'_opt
  then
   (dict', actx', dest_some $ astate'_opt)
  else raise Fail "transform_program failed to translate initial astate"
 end
;

end
