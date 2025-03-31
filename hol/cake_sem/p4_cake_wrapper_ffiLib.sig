signature p4_cake_wrapper_ffiLib =
sig
  include Abbrev

val translate_p4 : string -> term -> term -> term -> term -> bool -> unit

end
