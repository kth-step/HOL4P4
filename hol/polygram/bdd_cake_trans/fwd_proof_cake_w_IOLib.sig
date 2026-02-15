signature fwd_proof_w_IOcakeLib =
sig
  include Abbrev


        val convert_arith_policy_to_interval_tables_cake_w_IO : term * term * term * term * term -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

        
end