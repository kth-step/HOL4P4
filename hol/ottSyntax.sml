structure ottSyntax :> ottSyntax =
struct

open HolKernel Abbrev;

local open ottTheory in end;

val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott" "clause_name";

end
