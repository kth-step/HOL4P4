open p4newTheory;
open p4newSyntax;

open wordsSyntax;

val ERR = mk_HOL_ERR "p4new_execLib";
val wrap_exn = Feedback.wrap_exn "p4new_execLib";

(* Small-step verified executor: eval_p4_exp makes one reduction step. *)
local

val eval_p4_exp_errmsg_const = "Do not use eval_p4_exp to evaluate constants";
val eval_p4_exp_errmsg_unsupp = "Unsupported expression: ";
val eval_p4_exp_sub_errmsg_var = "Variables not supported yet";

in

fun eval_p4_exp exp (es, ts, st) = 
  if is_exp_bool_const exp
  then raise ERR "eval_p4_exp" eval_p4_exp_errmsg_const
  else if is_exp_int_const exp
  then raise ERR "eval_p4_exp" eval_p4_exp_errmsg_const
  else if is_exp_var exp
  then raise ERR "eval_p4_exp" (eval_p4_exp_errmsg_unsupp^((fst o dest_strip_comb) exp))
  else if is_exp_eq exp
  then raise ERR "eval_p4_exp" (eval_p4_exp_errmsg_unsupp^((fst o dest_strip_comb) exp))
  else if is_exp_sub exp
  then
    (* TODO: Get subtraction rule in less hard-coded fashion... *)
    eval_p4_binexp exp (es, ts, st) (dest_exp_sub, mk_word_sub,
                                     el 2 (CONJUNCTS exp_red_rules),
                                     el 3 (CONJUNCTS exp_red_rules),
                                     el 4 (CONJUNCTS exp_red_rules))
  else raise ERR "eval_p4_exp" (eval_p4_exp_errmsg_unsupp^((fst o dest_strip_comb) exp))
(* Unified function for all binary expressions on ints *)
and eval_p4_binexp binexp (es, ts, st) (dest_p4_binexp, mk_word_binexp, binexp_rule1, binexp_rule2, binexp_rule3) = 
  let
    val (op1, op2) = dest_p4_binexp binexp
  in
    if not (is_exp_int_const op1)
    then
      let
        val thm_exp_red = eval_p4_exp op1 (es, ts, st)
        val thm_spec = SIMP_RULE std_ss [ottTheory.clause_name_def] (SPECL [op1, op2, es, ts, st] binexp_rule1)
      in
        HO_MATCH_MP thm_spec thm_exp_red
      end
    else if not (is_exp_int_const op2)
    then
      let
        val thm_exp_red = eval_p4_exp op2 (es, ts, st)
        val thm_spec = SIMP_RULE std_ss [ottTheory.clause_name_def] (SPECL [op1, op2, es, ts, st] binexp_rule2)
      in
        HO_MATCH_MP thm_spec thm_exp_red
      end
    else
      let
        val int1 = dest_exp_int_const op1
        val int2 = dest_exp_int_const op2
        val int3_thm = wordsLib.WORD_ARITH_CONV (mk_word_binexp (int1, int2))
        val int3 = (rhs o concl) int3_thm
      in
        SIMP_RULE std_ss [ottTheory.clause_name_def, int3_thm] (SPECL [int1, int2, es, ts, st, int3] binexp_rule3)
      end
  end

end
;

(* TESTS:
val es = “es:env_stack”;
val ts = “ts:temp_stack”;
val st = “st:status”;

val exp = “exp_sub (exp_int_const 2w) (exp_int_const 1w)”;
val exp2 = “exp_sub (exp_sub (exp_int_const 2w) (exp_int_const 1w)) (exp_int_const 1w)”;
val exp3 = “exp_sub (exp_sub (exp_sub (exp_int_const 2w) (exp_int_const 1w)) (exp_int_const 1w)) (exp_int_const 1w)”;

val test = eval_p4_exp exp (es, ts, st);
val test2 = eval_p4_exp exp2 (es, ts, st);
val test3 = eval_p4_exp exp3 (es, ts, st);

val test4 = eval_p4_exp test3 (es, ts, st);
*)
