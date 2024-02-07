signature symb_execSyntax =
sig
  include Abbrev

val disj_list_tm : term
val mk_disj_list : term list -> term
val dest_disj_list : term -> term list
val is_disj_list : term -> bool

val mk_disj_list' : term -> term
val dest_disj_list' : term -> term

val symb_branch_cases_tm : term
val mk_symb_branch_cases : term * term -> term
val dest_symb_branch_cases : term -> term * term
val is_symb_branch_cases : term -> bool

end
