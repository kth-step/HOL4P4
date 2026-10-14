signature ottSyntax =
sig
  include Abbrev

val clause_name_tm : term
val dest_clause_name : term -> term
val is_clause_name : term -> bool
val mk_clause_name : term -> term

end
