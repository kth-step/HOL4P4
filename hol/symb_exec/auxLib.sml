structure auxLib :> auxLib = struct

open HolKernel Abbrev;

local open alistTheory in end;

(* TODO: Upstream? *)
val (alookup_tm,  mk_alookup, dest_alookup, is_alookup) =
  syntax_fns2 "alist" "ALOOKUP";

end
