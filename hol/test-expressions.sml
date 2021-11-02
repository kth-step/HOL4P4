open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open bitstringSyntax optionSyntax;
open p4Syntax;
open p4_exec_semTheory;
open testLib;
(* For EVAL-uating: *)
open blastLib;

(*****************************************************************************************)
(* This file includes some tests run on the HOL4-exported p4 expression reduction rules. *)
(*****************************************************************************************)

(*********)
(* Tests *)

(* These are the test values for the static tests *)
val width = 32;
val width_tm = numSyntax.term_of_int width;
(* w2v is used for legibility *)
val ev1 = mk_e_v $ mk_v_bitii (1, width);
val ev2 = mk_e_v $ mk_v_bitii (16384, width);

(* Static unary operations tests *)
val unary_test_cases = [
  (mk_e_unop (unop_compl_tm, ev1),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (4294967294,width))),
  (mk_e_unop (unop_neg_signed_tm, ev1),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (4294967295,width))),
  (mk_e_unop (unop_un_plus_tm, ev1),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (1,width)))
];

(* Test unary operations *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bit_word_well_formed", is_v_bit_word_well_formed width_tm)
                 unary_test_cases;

(* Static arithmetic tests *)
val arith_test_cases = [
  (mk_e_binop (ev1, binop_mul_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (16384,width))),
  (mk_e_binop (ev1, binop_div_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (0,width))),
  (mk_e_binop (ev1, binop_mod_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (1,width))),
  (mk_e_binop (ev1, binop_add_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (16385,width))),
  (mk_e_binop (ev1, binop_sub_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (4294950913,width))),
  (* Note: Testing shl might take a second or two *)
  (mk_e_binop (ev1, binop_shl_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (0,width))),
  (mk_e_binop (ev1, binop_shr_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (0,width))),
  (mk_e_binop (ev1, binop_and_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (0,width))),
  (mk_e_binop (ev1, binop_xor_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (16385,width))),
  (mk_e_binop (ev1, binop_or_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bitii (16385,width)))
];

(* Test arithmetic expressions *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bit_word_well_formed", is_v_bit_word_well_formed width_tm)
                 arith_test_cases;

(* Static predicate tests *)
val pred_test_cases = [
  (mk_e_binop (ev1, binop_le_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool T)),
  (mk_e_binop (ev1, binop_ge_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool F)),
  (mk_e_binop (ev1, binop_lt_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool T)),
  (mk_e_binop (ev1, binop_gt_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool F)),
  (mk_e_binop (ev1, binop_eq_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool F)),
  (mk_e_binop (ev1, binop_neq_tm, ev2),
   SOME (mk_some $ mk_e_v $ mk_v_bool T))
];

(* Test predicates *)
val _ = test_red ("eval_e", eval_e)
                 ("is_v_bool_well_formed", is_v_bool_well_formed)
                 pred_test_cases;

(* TODO: Test cases are only for bitvs and not Booleans *)
