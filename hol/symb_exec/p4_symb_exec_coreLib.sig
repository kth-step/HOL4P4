signature p4_symb_exec_coreLib =
sig
  include Abbrev

val packet_in_inner_consts : term list
val add_packet_in_stop_consts : term list -> term list

val approx_packet_in_extract :
   int -> term -> term -> term -> (thm * int list)
val approx_packet_in_lookahead :
   int -> term -> term -> term -> (thm * int list)
val approx_packet_in_advance :
   int -> term -> term -> term -> (thm * int list)

end
