signature p4_symb_execLib =
sig
  include Abbrev

val p4_symb_exec:
   bool ->
   hol_type ->
     (thm * term) ->
       (term * term) ->
         string list -> 
	   term ->
	     term list ->
	       term list -> thm -> (thm -> bool) option -> int -> symb_execLib.path_tree * (int * thm * thm) list

val p4_symb_exec_prove_contract:
   bool ->
   hol_type ->
     term -> (term * term) -> string list -> term -> term list -> term list -> thm -> (thm -> bool) option -> int -> term -> thm

val p4_debug_symb_exec:
   hol_type ->
     term ->
       (term * term) -> 
         string list -> 
	   term ->
	     term list ->
	       term list ->
		 thm ->
		   int ->
		     symb_execLib.path_tree *
		     (int * thm * (term * term * term * term)) list

val p4_debug_symb_exec_frame_lists:
   hol_type ->
     term ->
       (term * term) ->
         string list -> 
	   term ->
	     term list ->
	       term list -> thm -> int -> symb_execLib.path_tree * term list

end
