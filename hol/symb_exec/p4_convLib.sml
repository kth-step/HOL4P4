structure p4_convLib :> p4_convLib = struct
open HolKernel boolLib liteLib simpLib Parse bossLib;

open wordsSyntax computeLib;
open p4Syntax;
open evalwrapLib;

(* RESTR_HOL4P4_CONV constants: *)
val p4_stop_eval_consts_unary =
 [(* “word_1comp”, (* Should be OK? ¬v2w [x; F; T] = v2w [¬x; T; F] *) *)
(*
  “word_2comp:'a word -> 'a word”
*)
  word_2comp_tm
 ];
val p4_stop_eval_consts_binary =
 [
(*
“word_mul:'a word -> 'a word -> 'a word”,
  “word_div:'a word -> 'a word -> 'a word”,
  “word_mod:'a word -> 'a word -> 'a word”,
  “word_add:'a word -> 'a word -> 'a word”,
  “saturate_add:'a word -> 'a word -> 'a word”,
  “word_sub:'a word -> 'a word -> 'a word”,
  “saturate_sub:'a word -> 'a word -> 'a word”,
  “word_lsl_bv:'a word -> 'a word -> 'a word”, (* TODO: OK to evaluate if second operand has no free variables *)
  “word_lsr_bv:'a word -> 'a word -> 'a word”, (* TODO: OK to evaluate if second operand has no free variables *)
  (* “word_and”, (* Should be OK? w2v (v2w [x; F; T] && v2w [y; F; T]) = [x ∧ y; F; T] *) *)
  (* “word_xor”, (* Should be OK? w2v (v2w [x; F; T] ⊕ v2w [y; F; T]) = [x ⇎ y; F; F] *) *)
  (* “word_or”, (* Should be OK? w2v (v2w [x; F; T] ‖ v2w [y; F; T]) = [x ∨ y; F; T] *) *)
  “word_ls:'a word -> 'a word -> bool”,
  “word_hs:'a word -> 'a word -> bool”,
  “word_lo:'a word -> 'a word -> bool”,
  “word_hi:'a word -> 'a word -> bool”
*)
  word_mul_tm,
  word_div_tm,
  word_mod_tm,
  word_add_tm,
  saturate_add_tm,
  word_sub_tm,
  saturate_sub_tm,
  word_lsl_bv_tm,
  word_lsr_bv_tm,
  word_ls_tm,
  word_hs_tm,
  word_lo_tm,
  word_hi_tm
];

(* TODO: Merge with the below? *)
val table_stop_consts = [match_all_tm];

val p4_stop_eval_consts = p4_stop_eval_consts_unary@p4_stop_eval_consts_binary;


fun same_const_disj_list [] tm = K false tm
 | same_const_disj_list [x] tm = same_const x tm
 | same_const_disj_list (h::t) tm =
 same_const h tm orelse (same_const_disj_list t tm);

(* Customized CBV_CONV for HOL4P4 evaluation *)
local
(* TODO: Add back in when including p4_bigstep again
 val list_of_thys = ["p4_aux", "p4_core", "p4_v1model", "p4_ebpf", "p4_vss", "p4_bigstep"]
*)
 val list_of_thys = ["p4_aux", "p4_core", "p4_v1model", "p4_ebpf", "p4_vss"]

 fun filtered_thm_names name =
  (not $ String.isSuffix "_aux" name) andalso
  (not $ String.isSuffix "_AUX" name) andalso
  (not $ String.isSuffix "_primitive" name) andalso
  (not $ String.isSuffix "_primitive_def" name) andalso 
  (not $ String.isSuffix "_ind" name) andalso
  (not $ String.isSuffix "_UNION" name) andalso
  ((String.isSuffix "_def" name)) orelse
   (String.isSuffix "_11" name) orelse
   (String.isSuffix "_distinct" name)

 fun add_thy thy compset =
  let
   val thy_defs = definitions thy
   val thy_thms = thms thy
   val filtered_list =
    map snd $ filter (fn (name, thm) => filtered_thm_names name)
     (List.concat [thy_defs, thy_thms])
   val _ = map (fn thm => computeLib.add_thms [thm] compset handle ERR => ()) filtered_list
  in
   ()
  end;

 fun add_thy_list thys compset =
  let
   val _ = map (fn thy => add_thy thy compset) thys
  in
   ()
  end
 ;

 fun add_definitions thy compset =
  let
   val thy_defs =
    map snd $ filter (fn (name, thm) => filtered_thm_names name) (definitions thy)
   val thy_def_thms = map snd $ filter (fn (name, thm) => String.isSuffix "_def" name) (thms thy)
   val _ = map (fn thm => computeLib.add_thms [thm] compset) (thy_def_thms)
  in
   ()
  end
 ;

 val hol4p4_compset = reduceLib.num_compset ()
 val _ =
  foldl (fn (f, compset) => let val _ = f compset in compset end)
   hol4p4_compset
   [pairLib.add_pair_compset, optionLib.OPTION_rws, (wordsLib.add_words_compset true),
    stringLib.add_string_compset, alistLib.add_alist_compset]
 (* n2v loops on free variables, so it is only evaluate on concrete numbers (put before add_thy_list) *)
 val n2v_tm = prim_mk_const {Thy = "bitstring", Name = "n2v"}
 fun n2v_conv tm =
  if numSyntax.is_numeral (rand tm)
  then REWR_CONV bitstringTheory.n2v_def tm
  else raise (mk_HOL_ERR "p4_convLib" "n2v_conv" "symbolic argument")
 val _ = List.app (fn cs => ((computeLib.scrub_const cs n2v_tm handle _ => ());
                             computeLib.add_conv (n2v_tm, 1, n2v_conv) cs))
                  [hol4p4_compset, computeLib.the_compset]

 val _ = add_thy_list list_of_thys hol4p4_compset
 val _ = computeLib.add_thms [alistTheory.AFUPDKEY_def] hol4p4_compset
 (* TODO: Nice to have? *)
 val _ = computeLib.add_thms [sumTheory.INR_11, sumTheory.INL_11, sumTheory.INR_INL_11, sumTheory.INR_neq_INL] hol4p4_compset
(* TODO: Not the name in Trindemossen?
 val _ = computeLib.scrub_const hol4p4_compset “conc_red”
*)
(*
   val _ = Globals.max_print_depth := 9000;
   val _ = Globals.max_print_length := 9001;
   val to_compset_entries = List.filter (fn (name, transformations) => fst name = "conc_red_rules") $ listItems hol4p4_compset
*)

(* TODO: Scrub these? They look annoying...
 val _ = scrub_const hol4p4_compset “header_entries2v_UNION”
 val _ = scrub_const hol4p4_compset “deparameterise_tau_def_UNION”
 val _ = scrub_const hol4p4_compset “parameterise_tau_def_UNION”
*)

 local
  open clauses;
  open computeLib;

  fun is_conv transform =
   case transform of
    (RRules thmlist) => false
   | (Conversion conv) => true

  (* Annoying to see theorems multiple times. This removes at least
   * the most blatant duplication. *)
  fun filter_duplicate_thms _ [] = []
    | filter_duplicate_thms trs (h::t) =
     if (exists (fn thm => term_eq (concl h) (concl thm)) t) orelse
        (exists (fn thm => term_eq (concl h) (concl thm)) trs)
     then filter_duplicate_thms trs t
     else (h::(filter_duplicate_thms trs t))

  fun aggregate_thms l [] = l
   | aggregate_thms l (h::t) =
    case h of
    (RRules thmlist) =>
      aggregate_thms (thmlist@l) t 
    | (Conversion conv) =>
     aggregate_thms l t

  fun copy_compset_item_thms' old_thms new_transformations to_compset =
    let
     val new_thms = aggregate_thms [] new_transformations
     val _ = computeLib.add_thms (filter_duplicate_thms old_thms new_thms) to_compset
    in 
     ()
    end

  fun copy_compset_item_thms to_compset_items (name, transformations) to_compset =
   let
    val existing_entry_transformations =
     case List.find (fn (a,b) => a = name) to_compset_items of
       SOME entry => (aggregate_thms []) $ snd entry
     | NONE => []
   in
    copy_compset_item_thms' existing_entry_transformations transformations to_compset
   end
  ;

 in
 fun copy_compset_thms from_compset to_compset =
  let
   val from_compset_items = listItems from_compset

   val to_compset_items = listItems to_compset
(* Doesn't work if you filter out duplicate entries. This means that some necessary additions are to
 * existing same constants.
*)
(*
   val to_compset_entries = map fst $ listItems to_compset
   val from_compset_items = filter (fn (name, transformations) => not $ exists (fn el => name = el) to_compset_entries) from_compset_items
*)
  in
   foldl (fn (item, ()) => copy_compset_item_thms to_compset_items item to_compset) ()
    (from_compset_items)
  end
 end
 (* TODO: Brute-force solution. Fix later. *)
 val _ = copy_compset_thms computeLib.the_compset hol4p4_compset


 (* Adding a theorem to a compset again duplicates its rules, so the theories are added once *)
 val thys_in_the_compset = ref false
in
 fun get_HOL4P4_CONV thms_to_add =
  let
   val _ =
    if !thys_in_the_compset
    then ()
    else (add_thy_list list_of_thys the_compset; thys_in_the_compset := true)

   val _ = computeLib.add_thms thms_to_add hol4p4_compset
  in
   computeLib.CBV_CONV hol4p4_compset
  end
end

val HOL4P4_CONV = get_HOL4P4_CONV [];

val HOL4P4_TAC = CONV_TAC HOL4P4_CONV;

val HOL4P4_RULE = Conv.CONV_RULE HOL4P4_CONV;

(* TODO: Upstream the RESTR_CBV_CONV to main HOL4P4 repo? *)
fun RESTR_CBV_CONV compset clist =
  Lib.with_flag (stoppers, SOME (same_const_disj_list clist)) (CBV_CONV compset);

fun get_RESTR_HOL4P4_CONV thms_to_add clist =
  Lib.with_flag (stoppers, SOME (same_const_disj_list clist)) (get_HOL4P4_CONV thms_to_add);

val RESTR_HOL4P4_CONV = get_RESTR_HOL4P4_CONV [];

val RESTR_HOL4P4_CONV_stop_consts = RESTR_HOL4P4_CONV p4_stop_eval_consts;

fun p4_eval_ctxt_gen (stop_consts1, stop_consts2, mk_exec) path_cond astate =
 eval_ctxt_gen (stop_consts1@p4_stop_eval_consts@table_stop_consts) (stop_consts2@p4_stop_eval_consts) path_cond (mk_exec astate)
;

(* TODO: Fix naming for the three below, remove unnecessary abstraction *)
(* This is just evaluating a term and adding an assumption, without rewriting *)
(*
fun norewr_eval_ctxt_gen stop_consts ctxt tm =
  RESTR_HOL4P4_CONV stop_consts tm
  |> PROVE_HYP ctxt
  |> DISCH_CONJUNCTS_ALL
;
*)
(* The conversion is built once, not at every step *)
fun p4_get_norewr_eval_ctxt_gen (stop_consts, thms_to_add, mk_exec) =
 let
  val conv = get_RESTR_HOL4P4_CONV thms_to_add (stop_consts@p4_stop_eval_consts)
 in
  fn astate => conv (mk_exec astate)
 end
;

(* TODO: This should simplify the scopes after shortcutting *)
local
fun word_conv word =
 if null $ free_vars word
 then HOL4P4_CONV word
 else raise UNCHANGED
;

val word_convs_unary =
 map
 (fn wordop =>
  {conv = K (K word_conv),
   key= SOME ([], mk_comb (wordop, mk_var ("w", wordsSyntax.mk_word_type Type.alpha))),
   (* TODO: Better names *)
   name = term_to_string wordop,
   trace = 2}) p4_stop_eval_consts_unary
;
val word_convs_binary =
 map
 (fn wordop =>
  {conv = K (K word_conv),
   key= SOME ([], mk_comb (mk_comb (wordop, mk_var ("w", wordsSyntax.mk_word_type Type.alpha)), mk_var ("w'", wordsSyntax.mk_word_type Type.alpha))),
   (* TODO: Better names *)
   name = term_to_string wordop,
   trace = 2}) p4_stop_eval_consts_binary
;

in
val p4_wordops_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = word_convs_unary@word_convs_binary,
          dprocs = [],
          filter = NONE,
          name = SOME "p4_wordops_ss",
          rewrs = []};
end;
(*
val (id, path_cond_thm, step_thm) = el 1 path_cond_step_list
*)

end
