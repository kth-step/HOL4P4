signature fwd_proofLib =
sig
  include Abbrev

        val convert_arith_policy_to_interval_tables : term * term * term * term * term -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time
end