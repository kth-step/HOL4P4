signature symb_execLib =
sig
  include Abbrev

datatype path_tree = empty | node of int * thm * (path_tree list);

(* For debugging *)
val get_node : int -> path_tree -> path_tree option

val dbg_print : bool -> string -> unit

val symb_exec:
 bool * (bool -> thm -> thm) * thm * (int * thm -> (thm * int list) option) *
  (thm -> bool) -> thm -> int -> path_tree * (int * thm * thm) list

val symb_exec_conc:
   bool * (bool -> thm -> thm) * thm * (int * thm -> (thm * int list) option) *
    (thm -> bool) -> thm -> int -> int ->
     path_tree * (int * thm * thm) list

val prove_postconds: bool -> thm list -> term -> (int * thm * thm) list -> (int * thm) list

end
