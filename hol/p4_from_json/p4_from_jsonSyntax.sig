signature p4_from_jsonSyntax =
sig
  include Abbrev

val NONE_msg_tm   : term
val dest_NONE_msg : term -> term
val is_NONE_msg   : term -> bool
val mk_NONE_msg   : term -> term

val SOME_msg_tm   : term
val dest_SOME_msg : term -> term
val is_SOME_msg   : term -> bool
val mk_SOME_msg   : term -> term

end
