signature bdd_policy_cakeLib =
sig
  include Abbrev


        val convert_arith_policy_to_bdd : term * term * term * term * term * string -> thm

        
end