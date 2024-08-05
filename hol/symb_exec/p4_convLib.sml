structure p4_convLib :> p4_convLib = struct
(* OLD includes:
open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax numSyntax optionSyntax computeLib;

open p4Theory p4_exec_semTheory;
open symb_execTheory p4_symb_execTheory p4_bigstepTheory;

open p4Syntax p4_exec_semSyntax evalwrapLib p4_testLib symb_execSyntax;
open auxLib symb_execLib p4_bigstepSyntax;
*)
(* TODO: IF something is unexpectedly slower, could be because of missing opens here... *)
(* TODO: Note that this list of includes relies upon the heap that is used *)
open HolKernel boolLib liteLib simpLib Parse bossLib;

open computeLib;
open p4Syntax;
open evalwrapLib;

(* RESTR_HOL4P4_CONV constants: *)
val p4_stop_eval_consts_unary =
 [(* “word_1comp”, (* Should be OK? ¬v2w [x; F; T] = v2w [¬x; T; F] *) *)
  “word_2comp”
 ];
val p4_stop_eval_consts_binary =
 [“word_mul”,
  “word_div”,
  “word_mod”,
  “word_add”,
  “saturate_add”,
  “word_sub”,
  “saturate_sub”,
  “word_lsl_bv”, (* TODO: OK to evaluate if second operand has no free variables *)
  “word_lsr_bv”, (* TODO: OK to evaluate if second operand has no free variables *)
  (* “word_and”, (* Should be OK? w2v (v2w [x; F; T] && v2w [y; F; T]) = [x ∧ y; F; T] *) *)
  (* “word_xor”, (* Should be OK? w2v (v2w [x; F; T] ⊕ v2w [y; F; T]) = [x ⇎ y; F; F] *) *)
  (* “word_or”, (* Should be OK? w2v (v2w [x; F; T] ‖ v2w [y; F; T]) = [x ∨ y; F; T] *) *)
  “word_ls”,
  “word_hs”,
  “word_lo”,
  “word_hi”
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
 val list_of_thys = ["p4", "p4_aux", "p4_exec_sem",
		     "p4_core", "p4_v1model", "p4_ebpf", "p4_vss", "p4_bigstep"]

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


(* To compare between the two compsets:

(use p4_symb_exec_test1Script or similar to find an init_state)

Using hol4p4_compset:
   val test_thm = Lib.with_flag (stoppers, SOME (same_const_disj_list (stop_consts_never@p4_stop_eval_consts))) (computeLib.CBV_CONV hol4p4_compset) (mk_arch_multi_exec (ctx, astate, 1))

val astate2 = the_final_state test_thm

   val test_thm2 = Lib.with_flag (stoppers, SOME (same_const_disj_list (stop_consts_never@p4_stop_eval_consts))) (computeLib.CBV_CONV hol4p4_compset) (mk_arch_multi_exec (ctx, astate2, 1))

(* Doesn't seem the PMATCH conv is critical, since you can evaluate execution without it *)
 val _ = scrub_const computeLib.the_compset “PMATCH”
Using the_compset:
   Lib.with_flag (stoppers, SOME (same_const_disj_list (stop_consts_never@p4_stop_eval_consts))) (computeLib.CBV_CONV computeLib.the_compset) (mk_arch_multi_exec (ctx, init_astate, 2))


To display the transformations in the two different compsets:

 val _ = PolyML.print_depth 9001;

 val default_thms = fst $ unzip $ listItems computeLib.the_compset;

 val custom_thms = fst $ unzip $ listItems hol4p4_compset;

 val in_default_notin_custom = filter (fn thm => not $ exists (fn thm' => thm' = thm) custom_thms) default_thms;

 val in_custom_notin_default = filter (fn thm => not $ exists (fn thm' => thm' = thm) default_thms) custom_thms;

************************************************************

val convs_in_the_compset = List.filter (fn e => List.exists (fn e' => is_conv e') (snd e)) (listItems computeLib.the_compset)
val theories_with_convs = map (snd o fst) convs_in_the_compset

val convs_in_hol4p4_compset = List.filter (fn e => List.exists (fn e' => is_conv e') (snd e)) (listItems hol4p4_compset)
val theories_with_convs = map (snd o fst) convs_in_hol4p4_compset

*)

in
 fun get_HOL4P4_CONV thms_to_add =
  let
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
fun get_norewr_eval_ctxt_gen stop_consts thms_to_add tm =
  get_RESTR_HOL4P4_CONV thms_to_add stop_consts tm
;
fun p4_get_norewr_eval_ctxt_gen (stop_consts, thms_to_add, mk_exec) astate =
 get_norewr_eval_ctxt_gen (stop_consts@p4_stop_eval_consts) thms_to_add (mk_exec astate)
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
