signature fwd_proof_gen_eq_cake =
sig
  include Abbrev


        val gen_eq_policy_and_prove : term * term * term * term * string -> thm

        
end