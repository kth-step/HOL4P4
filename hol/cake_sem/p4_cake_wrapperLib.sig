signature p4_cake_wrapperLib =
sig
  include Abbrev

val translate_p4 : string -> term -> term -> term -> unit

end
