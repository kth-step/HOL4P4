open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(* TODO: Check which ones of these are really needed... *)
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory bitstringTheory wordsTheory;
open p4Theory;
open p4_exec_semTheory;
(* For EVAL-uating: *)
open blastLib;

(*****************************************************************************************)
(* This file includes some tests run on the HOL4-exported p4 expression reduction rules. *)
(*****************************************************************************************)
(* TODO: Remove all apostrophes and replace with proper syntax functions *)

(* TODO: Move to ottSyntax *)
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott"  "clause_name";

(******************)
(* Test functions *)

(* Simpset fragment containing a conversion keyed on bitvectors that will
 * rewrite bool lists as the v2w of the corresponding word *)
local
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
in
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
end;

(* Obtains result and evaluation theorem of expression *)
fun eval_e e_tm =
  let
    val res_thm = EVAL (``e_clos_exec (^e_tm) stacks status_running``) (* TODO: Alternatively, use a tailor-made eval_e_conv *)
    val res_canon_thm = SIMP_RULE (pure_ss++p4_v2w_ss) [] res_thm
    val res_canon_tm = rhs $ concl res_canon_thm
  in
    (* Present bool lists as w2v function on words *)
    (res_canon_tm, res_canon_thm)
  end
;

fun is_v_bool_well_formed res_opt =
  let
    (* Result is syntactically a SOME *)
    val res = optionSyntax.dest_some res_opt
    (* TODO: Hack, replace with syntactic functions *)
    val res_bs = snd $ dest_comb $ snd $ dest_comb res
  in
    ((term_eq res_bs T) orelse (term_eq res_bs F))
  end
;

fun is_v_bit_word_well_formed width res_opt =
  let
    (* Result is syntactically a SOME *)
    val res = optionSyntax.dest_some res_opt
    (* TODO: Hack, replace with syntactic functions *)
    val res_bs = snd $ dest_comb $ snd $ dest_comb res
    (* Bit-string is syntactically a pair *)
    val (res_w2v, res_width) = pairSyntax.dest_pair res_bs
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
  | test_red (f_name, f) (wf_name, wf) ((e_tm, exp_res)::t) =
  let
    val _ = print ((term_to_string e_tm)^ ":\n");
    val _ = print "===============================\n";
    val res = f e_tm
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

(* These are the test values for the static tests *)
val width = ``32``;
(* w2v is used for legibility *)
val ev1 = ``e_v (v_bit (w2v (1w:word32), 32))``;
val ev2 = ``e_v (v_bit (w2v (16384w:word32), 32))``;

(* More prototypes for manual testing:

val bl1 = (rhs o concl) (EVAL ``(extend F 32 [], 32)``); (* all zeroes *)
val bl2 = (rhs o concl) (EVAL ``(extend T 32 [], 32)``); (* all ones *)

val bl1 = ``([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
         F; F; F; F; F; F; F; F; T], 32)`` (* 1 *)
val bl2 = ``([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F;
         F; F; F; F; F; F; F; F; F], 32)`` (* 16384 *)

val stacks = ``stacks_tup ([]:scope list) ([]:(curr_stack_frame list))``;

*)

(* Static unary operations tests *)
(* TODO: Maker functions that just take unop_compl (in some form) and a number and word length *)
val unary_test_cases = [
  (``e_unop unop_compl (^ev1)``,
   SOME ``SOME (e_v (v_bit (w2v (0xFFFFFFFEw:word32),32)))``),
  (``e_unop unop_neg_signed (^ev1)``,
   SOME ``SOME (e_v (v_bit (w2v (0xFFFFFFFFw:word32),32)))``),
  (``e_unop unop_un_plus (^ev1)``,
   SOME ``SOME (e_v (v_bit (w2v (0x1w:word32),32)))``)
];

(* Test unary operations *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bit_word_well_formed", is_v_bit_word_well_formed width)
                 unary_test_cases;

(* Static arithmetic tests *)
val arith_test_cases = [
  (``e_binop (^ev1) binop_mul (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (16384w:word32),32)))``),
  (``e_binop (^ev1) binop_div (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (0w:word32),32)))``),
  (``e_binop (^ev1) binop_mod (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (1w:word32),32)))``),
  (``e_binop (^ev1) binop_add (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (16385w:word32),32)))``),
  (``e_binop (^ev1) binop_sub (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (0xFFFFC001w:word32),32)))``),
  (* Note: Testing shl might take a second or two *)
  (``e_binop (^ev1) binop_shl (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (0w:word32),32)))``),
  (``e_binop (^ev1) binop_shr (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (0w:word32),32)))``),
  (``e_binop (^ev1) binop_and (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (0w:word32),32)))``),
  (``e_binop (^ev1) binop_xor (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (16385w:word32),32)))``),
  (``e_binop (^ev1) binop_or (^ev2)``,
   SOME ``SOME (e_v (v_bit (w2v (16385w:word32),32)))``)
];

(* Test arithmetic expressions *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bit_word_well_formed", is_v_bit_word_well_formed width)
                 arith_test_cases;

(* Static predicate tests *)
val pred_test_cases = [
  (``e_binop (^ev1) binop_le (^ev2)``,
   SOME ``SOME (e_v (v_bool T))``),
  (``e_binop (^ev1) binop_ge (^ev2)``,
   SOME ``SOME (e_v (v_bool F))``),
  (``e_binop (^ev1) binop_lt (^ev2)``,
   SOME ``SOME (e_v (v_bool T))``),
  (``e_binop (^ev1) binop_gt (^ev2)``,
   SOME ``SOME (e_v (v_bool F))``),
  (``e_binop (^ev1) binop_eq (^ev2)``,
   SOME ``SOME (e_v (v_bool F))``),
  (``e_binop (^ev1) binop_neq (^ev2)``,
   SOME ``SOME (e_v (v_bool T))``)
];

(* Test predicates *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bool_well_formed", is_v_bool_well_formed)
                 pred_test_cases;

(* TODO: Test cases are only for bitvs and not Booleans *)

(*

  val clause_name_str = "e_add"
  val arg_l = [bl1, bl2];
  val stacks = ``stacks_tup ([]:scope list) ([]:(curr_stack_frame list))``;

reduce_e_arith clause_name_str arg_l stacks

*)
