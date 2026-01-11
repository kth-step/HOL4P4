signature fwd_proof_gen_eq_cake =
sig
  include Abbrev


        val gen_eq_policy_and_prove : term * term * term * term * string -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

        
end