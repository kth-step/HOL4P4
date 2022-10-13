signature p4_testLib =
sig
  include Abbrev

val mk_ipv4_packet_ok : term -> int -> term
val mk_eth_frame_ok : term -> term

val eval_and_print_result : term -> term -> int -> term
val eval_and_print_aenv : term -> term -> int -> term
val eval_and_print_rest : term -> term -> int -> term
val eval_under_assum :
   hol_type -> term -> term -> term list -> term list -> term list -> int -> thm
val dest_astate : term -> term * term * term * term
val dest_vss_aenv : term -> term * term * term * term
val dest_vss_actx :
   term ->
     term * term * term * term * term * term * term * term * term * term
val debug_arch_from_step :
   term ->
     term ->
       int ->
         (term * term * term * term * term * term * term * term * term * term)
         * ((term * term * term * term) * term * term * term)
val debug_frames_from_step :
   term ->
     term ->
       int ->
         (term * term * term * term * term * term) *
         (term * term * term * term)

end
