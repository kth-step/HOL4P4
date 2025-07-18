signature p4_exec_wrapper_ffiLib =
sig
  include Abbrev

val translate_p4 : string -> term -> term -> term -> bool -> bool -> unit

end
