signature p4_convLib =
sig
  include Abbrev

val HOL4P4_CONV : conv
val HOL4P4_TAC : tactic
val HOL4P4_RULE : thm -> thm
val add_HOL4P4_thms : thm list -> unit

val p4_stop_eval_consts : term list
val RESTR_HOL4P4_CONV : term list -> conv
val RESTR_HOL4P4_CONV_stop_consts : term -> thm

val p4_eval_ctxt_gen :
   term list * term list * ('a -> term) -> thm -> 'a -> thm
val p4_get_norewr_eval_ctxt_gen :
   term list * thm list * ('a -> term) -> 'a -> thm
val p4_wordops_ss : simpLib.ssfrag

end
