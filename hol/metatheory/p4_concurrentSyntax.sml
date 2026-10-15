structure p4_concurrentSyntax :> p4_concurrentSyntax =
struct

open HolKernel Abbrev pairSyntax;

local open p4_concurrentTheory in end;


val (trace_path_tm,  mk_trace_path, dest_trace_path, is_trace_path) =
  syntax_fns4 "p4_concurrent" "trace_path";

fun arch_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
  val aenv = list_mk_pair [n_externs, ext_obj_map, v_map, ctrl]
 in
  if tid = 1
  then list_mk_pair [
        list_mk_pair [index1, io, io', aenv],
        gscope1, arch_frame_list1, status1
       ]
  else list_mk_pair [
        list_mk_pair [index2, io, io', aenv],
        gscope2, arch_frame_list2, status2
       ]
 end
;

fun thread_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
 in
  if tid = 1
  then list_mk_pair [index1, gscope1, arch_frame_list1, status1]
  else list_mk_pair [index2, gscope2, arch_frame_list2, status2]
 end
;

end
