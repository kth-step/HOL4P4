structure evalwrapLib :> evalwrapLib =
struct

open HolKernel Parse boolLib bossLib;
open computeLib hurdUtils;

(*
 * This file offers functionality to evaluate a term given preconditions.
 * This is a copy of functionality hosted in the HolBA repository:
 *   https://github.com/kth-step/HOLBA
 *)

(* match types of free variables from preconditions  ctxt  and conclusion  tm *)
fun unify_same_free_vars ctxt tm =
  let
    fun nub ls = case ls of
      [] => [] | x::xs => x :: (nub $ filter (fn z => z <> x) xs)
    val cmp = fn x => fn y => String.compare (fst x, fst y) = LESS;
    val one_type = foldl Type.--> ``:bool``

    val ctxt_vars = nub $ map dest_var $ Term.free_vars ctxt
    val tm_vars = nub $ map dest_var $ Term.free_vars tm
    val ctxt_vars' = one_type $ map snd $ sort cmp
      $ filter (fn (name,_) => mem name $ map fst tm_vars) ctxt_vars
    val tm_vars' = one_type $ map snd $ sort cmp
      $ filter (fn (name,_) => mem name $ map fst ctxt_vars) tm_vars
    val unifier = type_unify ctxt_vars' tm_vars'
  in
    (Term.inst unifier ctxt, Term.inst unifier tm)
  end;

(*
 * evaluate a term  tm  in a non-empty context  ctxt : thm
 * given list of constants   stop_consts1  and  stop_consts2
 * whose definition should not be unfolded in the first and second evaluation
 * step, respectively.
 *)
fun eval_ctxt_gen stop_consts1 stop_consts2 ctxt tm =
  RESTR_EVAL_CONV stop_consts1 tm
  |> PROVE_HYP ctxt
  |> CONV_RULE $ RAND_CONV
    (REWRITE_CONV [ctxt] THENC RESTR_EVAL_CONV stop_consts2)
  |> DISCH_CONJUNCTS_ALL
;

(*
 * same as eval_ctxt_gen but unifies free variables in  ctxt_tm  and  tm ,
 * and expects  ctxt_tm  to be a conjunct
 * Example:
 *   eval_ctxt_gen [] ``f = (λx. x)`` ``f 1``
 * returns (as both f have different type)
 *   ⊢ ∀f f'. f' = (λx. x) ⇒ f 1 = f 1
 * while
 *   eval_ctxt_unify [] ``f = (λx. x)`` ``f 1``
 * returns the expected
 *   ⊢ ∀f. f = (λx. x) ⇒ f 1 = 1
 *)
fun eval_ctxt_unify stop_consts1 stop_consts2 ctxt_tm tm =
  let
    val (ctxt_tm,tm) = unify_same_free_vars ctxt_tm tm
  in
    eval_ctxt_gen stop_consts1 stop_consts2 (ASSUME ctxt_tm) tm
  end

(*
 * evaluate a term  tm  given a list of preconditions
 * Example:
 *   qeval_ctxt [`f 3n = 24n`]  `g o f:num -> num $ 1 + 2`
 * returns
 *   ⊢ ∀g f. f 3 = 24 ⇒ (g ∘ f) (1 + 2) = g 24: thm
 *)
fun qeval_ctxt ctxt tm =
  eval_ctxt_gen [] [] (ASSUME $ list_mk_conj $ map Term ctxt) (Term tm)

end
