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

val (arch_ebpf_tm, mk_arch_ebpf, dest_arch_ebpf, is_arch_ebpf) =
  syntax_fns1 "petr4_to_hol4p4" "arch_ebpf";

val arch_ebpf_NONE_tm = mk_arch_ebpf $ mk_none ``:ebpf_pkg_t``;

end
