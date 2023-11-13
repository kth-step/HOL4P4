signature p4_symb_execLib =
sig
  include Abbrev

val symb_exec:
   hol_type ->
     term -> term -> term list -> term list -> thm -> int -> (thm * thm) list

end
