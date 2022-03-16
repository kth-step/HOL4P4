signature p4_testLib =
sig
  include Abbrev

val mk_ipv4_packet_ok : term -> int -> term
val mk_eth_frame_ok : term -> term

end
