structure ottSyntax :> ottSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open ottTheory;

val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott" "clause_name";

end
