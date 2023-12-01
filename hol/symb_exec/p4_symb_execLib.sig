signature p4_symb_execLib =
sig
  include Abbrev

val p4_symb_exec:
   hol_type ->
     term ->
       term ->
         term list ->
           term list -> thm -> int -> symb_execLib.path_tree * (int * thm * thm) list

val p4_symb_exec_prove_contract:
   hol_type ->
     term -> term -> term list -> term list -> thm -> int -> term -> thm

end
