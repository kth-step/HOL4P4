signature p4_vssLib =
sig
  include Abbrev

val DROP_PORT_tm : term
val CPU_OUT_PORT_tm : term

val vss_input_f : term
val vss_output_f : term

val vss_ext_map : term
val vss_ffblock_map : term

end
