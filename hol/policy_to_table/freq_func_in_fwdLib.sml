structure freq_func_in_fwdLib :> freq_func_in_fwdLib = struct

open HolKernel Parse;


fun write_term_to_file (filename, tm) =
    let
        (* Convert term to string - using HOL's term_to_string *)
        val content = term_to_string tm
        val outstream = TextIO.openOut filename
        val _ = TextIO.output(outstream, content)
        val _ = TextIO.closeOut outstream
    in
        ()
    end
    handle e => (TextIO.closeOut (TextIO.openOut filename); raise e)



fun time_stage (stage_name, timer_cpu, timer_real) =
    let
        val cpu_time = Timer.checkCPUTimer timer_cpu
        val real_time = Timer.checkRealTimer timer_real
        val _ = HOL_MESG (stage_name ^ " completed in: " ^
                      Time.toString (#usr cpu_time) ^ " user, " ^
                      Time.toString (#sys cpu_time) ^ " system, " ^
                      Time.toString real_time ^ " real\n")
    in
        (cpu_time, real_time)
    end


end;
