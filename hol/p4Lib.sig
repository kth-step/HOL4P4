signature p4Lib =
sig
  include Abbrev

val fupdate_subterm_NORMALISE_CONV : Abbrev.conv

val FMAP_ss : simpLib.ssfrag

val get_clause_assums : thm -> term list
val find_clause : thm -> string -> thm option
val find_clause_e_red : string -> thm option
val find_clause_stmt_red : string -> thm option
val find_clause_frames_red : string -> thm option
val find_clause_arch_red : string -> thm option

end
