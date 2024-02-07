structure symb_execSyntax :> symb_execSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib listSyntax;

open symb_execTheory;

val (disj_list_tm,  mk_disj_list', dest_disj_list', is_disj_list) =
  syntax_fns1 "symb_exec" "disj_list";

fun mk_disj_list list = mk_disj_list' $ mk_list (list, bool);

fun dest_disj_list list = fst $ dest_list $ dest_disj_list' list;

val (symb_branch_cases_tm,
     mk_symb_branch_cases,
     dest_symb_branch_cases,
     is_symb_branch_cases) =
 syntax_fns2 "symb_exec" "symb_branch_cases";

end
