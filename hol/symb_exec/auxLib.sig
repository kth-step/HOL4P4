signature auxLib =
sig
  include Abbrev

val alookup_tm : term
val dest_alookup : term -> term * term
val is_alookup : term -> bool
val mk_alookup : term * term -> term

end
