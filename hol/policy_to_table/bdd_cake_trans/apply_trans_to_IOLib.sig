signature apply_trans_to_IOLib =
sig
  include Abbrev

   val sptrees_gen_bdds_policy_and_table : term * term * term -> (term * term * term)
   val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

end