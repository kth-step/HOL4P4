signature apply_trans_to_IOLib =
sig
  include Abbrev

   val sptrees_gen_bdds_policy_and_table : term * term * term -> (term * term * term)

end