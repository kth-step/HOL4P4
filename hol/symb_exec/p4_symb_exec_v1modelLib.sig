signature p4_symb_exec_v1modelLib =
sig
  include Abbrev

val approx_v1model_register_construct :
   string -> int -> term -> (thm * int list) option
val approx_v1model_register_read :
   string -> int -> term -> term -> (thm * int list) option
val approx_v1model_update_checksum :
   string -> int -> term -> (thm * int list) option

end
