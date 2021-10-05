open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(* TODO: Check which ones of these are really needed... *)
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;
open bitstringTheory;
open wordsTheory;
open p4Theory;

(*****************************************************************************************)
(* This file includes some tests run on the HOL4-exported p4 expression reduction rules. *)
(*****************************************************************************************)

(* TODO: Move to ottSyntax *)
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott"  "clause_name";

(************************)
(* Evalation functions *)

(* eval_e_conv is a sketch for what might be used as an alternative to EVAL
 * if it should prove too slow *)

val p4_e_thms =
  [bitv_unop_def,
   bitv_bl_unop_def,
   get_word_unop_def,
   bitv_binop_def,
   bitv_bl_binop_def,
   bitv_binop_inner_def,
   get_word_binop_def,
   bitv_binpred_def,
   bitv_binpred_inner_def,
   get_word_binpred_def];

val p4_w2v_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K computeLib.EVAL_CONV),
                    key= SOME ([], ``w2v w``),
                    name = "EVAL_CONV_W2V",
                    trace = 2}],
                    dprocs = [],
          filter = NONE,
          name = SOME "p4_w2v_ss",
          rewrs = []};
val p4_v2n_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K computeLib.EVAL_CONV),
                    key= SOME ([], ``v2n v``),
                    name = "EVAL_CONV_V2N",
                    trace = 2}],
                    dprocs = [],
          filter = NONE,
          name = SOME "p4_v2n_ss",
          rewrs = []};

(* TODO: Utilize bitstringTheory.w2v_v2w for nested expressions properly *)
(* Meant to simplify the RHS of rule assumptions for concrete arithmetic *)
fun eval_e_conv e = 
  let
    (* Rewrite the P4-specific stuff *)
    (* v2w_n2w_ss: v2w and n2w only *)
    (* BITSTRING_GROUND_ss: band, bxor, bor, ... *)
    (* TODO: shift operations can take a lot of time for large numbers, why? *)
    (*       v2n function efficiently evaluatable... *)
    val thm1 = SIMP_CONV (std_ss++bitstringLib.v2w_n2w_ss++bitstringLib.BITSTRING_GROUND_ss) p4_e_thms e
    (* Do the word arithmetic *)
    (* TODO: Might mess up LHS *)
    val thm2 = blastLib.BBLAST_RULE thm1
  in
    (* Use a simpset that pattern matches on w2v and evaluates those parts *)
    SIMP_RULE (std_ss++p4_w2v_ss++p4_v2n_ss) [] thm2
  end
;

(******************)
(* Test functions *)

(* Obtains a list of assumptions for a reduction clause *)
fun get_clause_assums thm =
  (strip_conj o fst o dest_imp o concl o SPEC_ALL) thm
;

(* Finds the rule with name clause_name_str in a red_rules-theorem exported from ott *)
fun find_clause clause_name_str thm =
  let
    val clause_name_str_tm = stringSyntax.fromMLstring clause_name_str
    val conj_thms = CONJUNCTS thm
  in
    List.find ((fn assums => isSome (List.find (fn tm => if is_clause_name tm then term_eq (dest_clause_name tm) clause_name_str_tm else false) assums)) o get_clause_assums) conj_thms
  end
;

val bitv = ``([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; T],32)``

fun to_bitv_word_form bitv =
  let
    val (vector, width) = pairSyntax.dest_pair bitv
    val word = wordsSyntax.mk_wordi (bitstringSyntax.num_of_term vector, numSyntax.int_of_term width)
    val bitv_word = bitstringSyntax.mk_w2v word
    val bitv' = pairSyntax.mk_pair (bitv_word, width)
  in
    bitv'
  end
;

fun to_bitv_word_form_conv bitv =
  let
    val bitv_word = to_bitv_word_form bitv
    val bitv_word_thm = GSYM (EVAL bitv_word)
  in
    bitv_word_thm
  end
;

val p4_v2w_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K to_bitv_word_form_conv),
                    key= SOME ([], ``(v:bool list, 32)``),
                    name = "BITV_TO_WORD_FORM",
                    trace = 2}],
                    dprocs = [],
          filter = NONE,
          name = SOME "p4_v2w_ss",
          rewrs = []};

(* Obtains result and evaluation theorem of concrete arithmetic expression,
 * given reduction clause name and two concrete bitvs *)
fun eval_e clause_name_str arg_l =
  case (find_clause clause_name_str e_red_rules) of
    NONE => NONE (* TODO: Provide feedback? *)
  | SOME add_conj =>
    let
      val add_conj2 = SPECL arg_l add_conj
      val add_conj3 = SPEC_ALL add_conj2
      val (add_conj_ass_tm, _) = dest_imp (concl add_conj3)
      val add_conj_ass_tm_l = strip_conj add_conj_ass_tm
      (* Filter out clause_name conjuncts *)
      val add_conj_ass_tm_l2 = filter (fn tm => not (is_clause_name tm)) add_conj_ass_tm_l

      (* TODO: Currently, only first antecedent will be treated.
       *       More generally, the below should treat all antecedents of the rule and
       *       maybe use specific conversions to prove them, not just EVAL. *)
      val ass_tm = (el 1 add_conj_ass_tm_l2)
      val res_thm = EVAL (lhs ass_tm) (* TODO: Alternatively, use a tailor-made eval_e_conv *)


      (* The below allows for both option-results (using wordsTheory under the hood) and
       * non-option results (using bitstringTheory) *)
      val res_tm = if optionSyntax.is_some ((rhs o concl) res_thm)
                   then optionSyntax.dest_some ((rhs o concl) res_thm)
                   else ((rhs o concl) res_thm)
      val res_canon_tm = if pairSyntax.is_pair res_tm
                         then to_bitv_word_form res_tm
                         else res_tm
    in
      (* Canonical format of bool lists is w2v function from words *)
      SOME (res_canon_tm, SIMP_RULE (pure_ss++p4_v2w_ss) [] res_thm)
    end
;

fun is_boolv_well_formed res =
  ((term_eq res T) orelse (term_eq res F))
;

(* Checks well-formedness of reduction result with respect to some width *)
(* TODO: Add more informative feedback *)
fun is_bitv_well_formed width res =
  let
    (* Result is syntactically a pair *)
    val (res_vector, res_width) = pairSyntax.dest_pair res
    (* Width of result matches expected width *)
    val width_ok = (term_eq res_width width) 
    (* Result vector is syntactically a list *)
    val (res_vector_list, res_vector_t) = listSyntax.dest_list res_vector
    (* Result vector has expected length *)
    val vector_list_length_ok = ((length res_vector_list) = (numSyntax.int_of_term width))
    (* Result vector elements are syntactically T or F *)
    val vector_elements_ok = not (exists (fn el => not (is_boolv_well_formed el)) res_vector_list)
  in
    (width_ok andalso vector_list_length_ok andalso vector_elements_ok)
  end
;

fun is_bitv_word_well_formed width res =
  let
    (* Result is syntactically a pair *)
    val (res_w2v, res_width) = pairSyntax.dest_pair res
    (* Width of result matches expected width *)
    val width_ok = (term_eq res_width width)
 
    (* Result w2v word is syntactically a word literal *)
    val res_w = bitstringSyntax.dest_w2v res_w2v
    val literal_ok = wordsSyntax.is_word_literal res_w

    (* Result w2v word has expected size *)
    val size_ok = ((wordsSyntax.size_of res_w) = (numSyntax.dest_numeral width))
  in
    (width_ok andalso literal_ok andalso size_ok)
  end
;


(* This tests all test cases in a provided list using antecedent-evaluation function f
 * and well-formedness function wf *)
fun test_red _ _ [] = ()
  | test_red (f_name, f) (wf_name, wf) ((clause_name, args, exp_res)::t) =
  let
    val _ = print (clause_name ^ ":\n");
    val _ = print "===============================\n";
    val res_opt = f clause_name args
    val res = if isSome res_opt then valOf res_opt else
              raise Fail ("test_red::"^(f_name)^" failed to produce a result")
    val _ = if wf (fst res) then () else
            raise Fail ("test_red::the result is not well-formed according to "^(wf_name))
    val _ = (Hol_pp.print_thm (snd res); print "\n");
    val _ = if isSome exp_res
            then if identical (fst res) (valOf exp_res) then () else
                 raise Fail "test_red::reduction does not have expected result"
            else ()
    val _ = print "\n\n";
  in
    (test_red (f_name, f) (wf_name, wf) t)
  end;

(*********)
(* Tests *)

(* TODO: ss keyed on bool lists, transforming to words? *)

(* These are the test vectors for the static tests *)
val width = ``32``;
(* w2v is used for legibility *)
val bl1 = ``(w2v (1w:word32), 32)``;
val bl2 = ``(w2v (16384w:word32), 32)``;

(* More prototypes for manual testing:

val bl1 = (rhs o concl) (EVAL ``(extend F 32 [], 32)``); (* all zeroes *)
val bl2 = (rhs o concl) (EVAL ``(extend T 32 [], 32)``); (* all ones *)

val bl1 = ``([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
         F; F; F; F; F; F; F; F; T], 32)`` (* 1 *)
val bl2 = ``([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F;
         F; F; F; F; F; F; F; F; F], 32)`` (* 16384 *)

*)

(* Prototypes for manually testing evaluatability:

EVAL ``bitv_unop unop_neg_signed (^bl1)``;
EVAL ``bitv_binop binop_mul (^bl1) (^bl2)``;
EVAL ``bitv_binop binop_add (^bl1) (^bl2)``;

EVAL ``bitv_binop binop_add (w2v (2w:word32), 32) (w2v (3w:word32), 32)``;
EVAL ``bitv_binop binop_mul (w2v (2w:word32), 32) (w2v (3w:word32), 32)``;

EVAL ``bitv_binop binop_add (THE (bitv_binop binop_add (w2v (2w:word32), 32) (w2v (3w:word32), 32))) (w2v (3w:word32), 32)``;
*)

(* Static unary operations tests *)
val unary_test_cases = [
  ("e_compl", [bl1],
   SOME ``(w2v (0xFFFFFFFEw:word32),32)``),
  ("e_neg_signed", [bl1],
   SOME ``(w2v (0xFFFFFFFFw:word32),32)``),
  ("e_un_plus",  [bl1],
   SOME ``(w2v (0x1w:word32),32)``)
];

(* Test unary operations *)
val _ = test_red ("eval_e", eval_e)
                 ("is_bitv_word_well_formed", is_bitv_word_well_formed width)
                 unary_test_cases;

(* Static arithmetic tests *)
val arith_test_cases = [
  ("e_mul", (* Name of reduction clause *)
   [bl1, bl2], (* Arguments to expression *)
   SOME ``(w2v (16384w:word32),32)``), (* Expected result *)
  ("e_div", [bl1, bl2],
   SOME ``(w2v (0w:word32),32)``),
  ("e_mod",  [bl1, bl2],
   SOME ``(w2v (1w:word32),32)``),
  ("e_add", [bl1, bl2],
   SOME ``(w2v (16385w:word32),32)``),
  ("e_sub", [bl1, bl2],
   SOME ``(w2v (0xFFFFC001w:word32),32)``),
  (* Note: Testing shl might take a second or two *)
  ("e_shl", [bl1, bl2],
   SOME ``(w2v (0w:word32),32)``),
  ("e_shr", [bl1, bl2],
   SOME ``(w2v (0w:word32),32)``),
  ("e_and", [bl1, bl2],
   SOME ``(w2v (0w:word32),32)``),
  ("e_or", [bl1, bl2],
   SOME ``(w2v (16385w:word32),32)``),
  ("e_xor", [bl1, bl2],
   SOME ``(w2v (16385w:word32),32)``)
];

(* Test arithmetic expressions *)
val _ = test_red ("eval_e", eval_e)
                 ("is_bitv_word_well_formed", is_bitv_word_well_formed width)
                 arith_test_cases;

(* Static predicate tests *)
val pred_test_cases = [
  ("e_le",
   [bl1, bl2],
   SOME ``T``),
  ("e_ge",
   [bl1, bl2],
   SOME ``F``),
  ("e_lt",
   [bl1, bl2],
   SOME ``T``),
  ("e_gt",
   [bl1, bl2],
   SOME ``F``),
  ("e_eq",
   [bl1, bl2],
   SOME ``F``),
  ("e_neq",
   [bl1, bl2],
   SOME ``T``)
];

(* Test predicates *)
val _ = test_red ("eval_e", eval_e)
                 ("is_boolv_well_formed", is_boolv_well_formed)
                 pred_test_cases;

(* TODO: Test cases are only for bitvs and not Booleans *)

(* Showcase of how eval_e can be used to compute reductions *)
fun reduce_e_arith clause_name_str arg_l stacks =
  case (find_clause clause_name_str e_red_rules) of
    NONE => NONE (* TODO: Provide feedback? *)
  | SOME clause =>
    let
      val arith_res = eval_e clause_name_str arg_l
      val (arith_res_tm, arith_res_thm) =
        if isSome arith_res
        then valOf arith_res
        else raise Fail "Evaluation of antecedent of reduction rule unsuccessful"
      val clause2 = REWRITE_RULE [ottTheory.clause_name_def] clause
      val clause3 = HO_MATCH_MP clause2 arith_res_thm
      val clause4 = SPEC stacks clause3
    in
      SOME clause4
    end
;

(*
  val clause_name_str = "e_add"
  val arg_l = [bl1, bl2];
  val stacks = ``stacks_tup ([]:scope list) ([]:(curr_stack_frame list))``;

reduce_e_arith clause_name_str arg_l stacks
*)
