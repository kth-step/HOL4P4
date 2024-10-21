structure petr4_to_hol4p4Syntax :> petr4_to_hol4p4Syntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax listSyntax
     wordsSyntax numSyntax bitstringSyntax;
open petr4_to_hol4p4Theory;

val (SOME_msg_tm, mk_SOME_msg, dest_SOME_msg, is_SOME_msg) =
  syntax_fns1 "petr4_to_hol4p4" "SOME_msg";

val (NONE_msg_tm, mk_NONE_msg, dest_NONE_msg, is_NONE_msg) =
  syntax_fns1 "petr4_to_hol4p4" "NONE_msg";


val (arch_vss_tm, mk_arch_vss, dest_arch_vss, is_arch_vss) =
  syntax_fns1 "petr4_to_hol4p4" "arch_vss";

val arch_vss_NONE_tm = mk_arch_vss $ mk_none ``:vss_pkg_t``;

val (vss_pkg_VSS_tm, mk_vss_pkg_VSS, dest_vss_pkg_VSS, is_vss_pkg_VSS) =
  syntax_fns1 "petr4_to_hol4p4" "vss_pkg_VSS";


val (arch_ebpf_tm, mk_arch_ebpf, dest_arch_ebpf, is_arch_ebpf) =
  syntax_fns1 "petr4_to_hol4p4" "arch_ebpf";

val arch_ebpf_NONE_tm = mk_arch_ebpf $ mk_none ``:ebpf_pkg_t``;

val (ebpf_pkg_ebpfFilter_tm, mk_ebpf_pkg_ebpfFilter, dest_ebpf_pkg_ebpfFilter, is_ebpf_pkg_ebpfFilter) =
  syntax_fns1 "petr4_to_hol4p4" "ebpf_pkg_ebpfFilter";


val (arch_v1model_tm, mk_arch_v1model, dest_arch_v1model, is_arch_v1model) =
  syntax_fns1 "petr4_to_hol4p4" "arch_v1model";

val arch_v1model_NONE_tm = mk_arch_v1model $ mk_none ``:v1model_pkg_t``;

val (v1model_pkg_V1Switch_tm, mk_v1model_pkg_V1Switch, dest_v1model_pkg_V1Switch, is_v1model_pkg_V1Switch) =
  syntax_fns2 "petr4_to_hol4p4" "v1model_pkg_V1Switch";


val (arch_xsa_tm, mk_arch_xsa, dest_arch_xsa, is_arch_xsa) =
  syntax_fns1 "petr4_to_hol4p4" "arch_xsa";

val arch_xsa_NONE_tm = mk_arch_xsa $ mk_none ``:xsa_pkg_t``;

val (xsa_pkg_pipe_tm, mk_xsa_pkg_pipe, dest_xsa_pkg_pipe, is_xsa_pkg_pipe) =
  syntax_fns2 "petr4_to_hol4p4" "xsa_pkg_pipe";

end
