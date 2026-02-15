signature fwd_proof_polcies_cakeLib =
sig
  include Abbrev


        val check_two_polcies_eq : term * term * term * term * term * string -> thm

        
end