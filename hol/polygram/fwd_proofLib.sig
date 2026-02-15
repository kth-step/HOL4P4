signature fwd_proofLib =
sig
  include Abbrev

        val convert_arith_policy_to_interval_tables : term * term * term * term * term -> thm

end