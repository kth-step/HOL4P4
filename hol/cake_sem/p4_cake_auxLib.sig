signature p4_cake_auxLib =
sig
  include Abbrev

val BOOL_LIST_ss : simpLib.ssfrag

val BOOL_LIST_ss' : simpLib.ssfrag

val v1model_get_input :
   term -> (string * int) list -> string list -> term

val invert_dict : term -> term

val deparse_bool_list : term -> string

val parse_bool_list : string -> term

end
