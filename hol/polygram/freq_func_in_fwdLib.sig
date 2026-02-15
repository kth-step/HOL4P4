signature freq_func_in_fwdLib =
sig

          val write_term_to_file : string * Parse.term -> unit
          val time_stage : string * Timer.cpu_timer * Timer.real_timer -> {sys: Time.time, usr: Time.time} * Time.time

end