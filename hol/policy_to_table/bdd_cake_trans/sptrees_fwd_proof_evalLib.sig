signature sptrees_fwd_proof_evalLib =
sig
  include Abbrev


        val eval_sptrees_convert_arith_policy_to_interval_tables : term * term * term * term * term -> thm
        val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time
        
end