signature testLib =
sig
  include Abbrev

val p4_v2w_ss : simpLib.ssfrag

val eval_e : term -> term * thm

val is_v_bool_well_formed : term -> bool

val is_v_bit_word_well_formed : term -> term -> bool

val test_red :
   'a * (term -> term * thm) ->
     string * (term -> bool) -> (term * term option) list -> unit

end
