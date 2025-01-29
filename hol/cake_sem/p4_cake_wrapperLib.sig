signature p4_cake_wrapperLib =
sig
  include Abbrev

val translate_p4 : string -> term -> term -> term -> unit

val append_prog_p4_wrapper : unit -> term

end
