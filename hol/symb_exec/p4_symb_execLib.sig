signature p4_symb_execLib =
sig
  include Abbrev

datatype defn_data =
   def_term of term
 | def_thm of thm;

val p4_symb_exec:
   int ->
   bool ->
   hol_type ->
     (thm * term) ->
       (term * term * term) ->
         string list ->
           thm list ->
	     term ->
	       term list ->
		 term list -> thm list -> thm -> (thm -> bool) option -> int -> symb_execLib.path_tree * (int * thm * thm) list

val p4_symb_exec_prove_contract:
   bool ->
   hol_type ->
     defn_data -> (term * term * term) -> string list -> thm list -> term -> term list -> term list -> thm list -> thm -> (thm -> bool) option -> int -> term -> thm list -> thm

val p4_symb_exec_prove_contract_conc:
   bool ->
   hol_type ->
     defn_data -> (term * term * term) -> string list -> thm list ->
       term -> term list -> term list -> thm list -> thm -> (thm -> bool) option -> int -> term -> thm list -> thm

val p4_debug_symb_exec:
   hol_type ->
     defn_data ->
       (term * term * term) -> 
         string list -> thm list ->
	   term ->
	     term list ->
	       term list ->
                thm list -> 
		  thm ->
		    int ->
		      symb_execLib.path_tree *
		      (int * thm * (term * term * term * term)) list

val p4_debug_symb_exec_frame_lists:
   hol_type ->
     defn_data ->
       (term * term * term) ->
         string list -> thm list ->
	   term ->
	     term list ->
	       term list -> thm list -> thm -> int -> symb_execLib.path_tree * term list

val get_v1model_wellformed_defs : term -> term -> Defn.defn

val p4_combine_contracts: thm -> thm -> thm -> thm

end
