signature fwd_proof_cakeLib =
sig
  include Abbrev


        val convert_arith_policy_to_interval_tables_cake : term * term * term * term * term * string -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

        
end