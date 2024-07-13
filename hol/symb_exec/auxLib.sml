structure auxLib :> auxLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib listSyntax;

open alistTheory;

(* TODO: Upstream? *)
val (alookup_tm,  mk_alookup, dest_alookup, is_alookup) =
  syntax_fns2 "alist" "ALOOKUP";

end
