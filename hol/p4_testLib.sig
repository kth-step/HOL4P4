signature p4_testLib =
sig
  include Abbrev

val mk_ipv4_packet_ok : term -> int -> term
val mk_ipv4_packet_ok_ttl : term -> int -> term
val mk_eth_frame_ok : term -> term

val get_actx : thm -> term
val simple_arith_ss : simpLib.simpset
val the_final_state_imp : thm -> term

val eval_and_print_result : string -> term -> term -> int -> term
val eval_and_print_aenv : string -> term -> term -> int -> term
val eval_and_print_rest : string -> term -> term -> int -> term
val eval_under_assum :
   hol_type -> term -> term -> term list -> term list -> thm -> int -> thm
val eval_under_assum_break : term -> term -> term list -> thm -> int list -> thm
val dest_ascope : term -> term * term * term * term
val dest_actx :
   term ->
     term * term * term * term * term * term * term * term * term * term
val debug_arch_from_step :
   string ->
   term ->
     term ->
       int ->
         (term * term * term * term * term * term * term * term * term * term)
         * ((term * term * term * term) * term * term * term)
val debug_frames_from_step :
   string ->
   term ->
     term ->
       int ->
         (term * term * term * term * term * term) *
         (term * term * term * term)
val the_final_state : thm -> term
val the_final_state_hyp_imp : thm -> term * term
val p4_eval_test_tac : hol_type -> term -> term -> tactic

val eval_step_fuel : hol_type -> term -> term -> int -> thm
val eval_step : hol_type -> term -> term -> thm

val get_trace_thread_n : string -> term -> term -> int -> int -> thm
val get_trace_thread_next_n : string -> term -> thm -> int -> int -> thm

end
