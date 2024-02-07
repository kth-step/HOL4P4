signature symb_execLib =
sig
  include Abbrev

datatype path_tree = empty | node of int * thm * (path_tree list);

val symb_exec:
 (thm * thm -> thm) * thm * (thm -> thm option) *
  (thm -> bool) -> thm -> int -> path_tree * (int * thm * thm) list

end
