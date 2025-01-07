signature p4_cake_auxLib =
sig
  include Abbrev

val BOOL_LIST_ss : ssfrag

val BOOL_LIST_ss' : ssfrag

val v1model_get_input :
   term -> (string * int) list -> string list -> term

end
