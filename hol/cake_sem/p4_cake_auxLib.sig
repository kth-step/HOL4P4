signature p4_cake_auxLib =
sig
  include Abbrev

val identifier : hol_type

val matching_optimization : bool

val get_id : string -> term

val cake_dict_tm : term

val BOOL_LIST_ss : simpLib.ssfrag

val BOOL_LIST_ss' : simpLib.ssfrag

val v1model_get_input :
   term -> (string * int) list -> string list -> term

val invert_dict : term -> term

val deparse_bool_list : term -> string

val parse_bool_list : string -> term

val hex_to_bool_list : string -> term

val bool_list_to_hex : term -> string

val populate_table : term -> Random.generator -> int -> term

end
