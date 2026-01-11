signature fwd_proof_polcies_cakeLib =
sig
  include Abbrev


        val check_two_polcies_eq : term * term * term * term * term * string -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

        
end