structure p4Lib :> p4Lib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;
open finite_mapLib;
open finite_mapSyntax;

open p4Theory;

(* Reduces all finite maps with updates to a representation
 * which shows only the last updates to any key *)
local
fun fupdate_subterm_NORMALISE tm =
 if is_fupdate tm
 then
  let
   val thm = fupdate_NORMALISE_CONV tm
   val (lhs, rhs) = dest_eq $ concl thm
  in
   if term_eq lhs rhs
   then TRUTH
   else thm
  end
 else
  if is_comb tm
  then
   let
     val (next1, next2) = dest_comb tm
     val next_thm1 = fupdate_subterm_NORMALISE next1
     val next_thm2 = fupdate_subterm_NORMALISE next2
   in
     if not (term_eq (concl next_thm1) T)
     then REWRITE_CONV [next_thm1] tm
     else if not (term_eq (concl next_thm2) T)
	  then REWRITE_CONV [next_thm2] tm
	  else TRUTH
   end
  else TRUTH
in
fun fupdate_subterm_NORMALISE_CONV tm =
 let
  val thm = fupdate_subterm_NORMALISE tm
 in
  if term_eq (concl thm) T
  then raise UNCHANGED
  else thm
 end
end
;

(* Simpset fragment that applies fupdate_subterm_NORMALISE_CONV
 * to all finite maps *)
val FMAP_ss =
 SSFRAG {name = SOME "FMAP_ss",
	 convs = [{conv = K (K fupdate_subterm_NORMALISE_CONV),
		   key= SOME ([], mk_var ("fmap", mk_fmap_ty (Type.alpha, Type.beta))),
		   name = "fupdate_subterm_NORMALISE_CONV",
		   trace = 2}],
	 rewrs = [],
         ac = [],
	 filter = NONE,
	 dprocs = [],
	 congs = []
 };

(* Example of usage:

open stringTheory;

Theorem fmap_ss_test:
 (FEMPTY |+ ("a",3) |+ ("b",2)) = (FEMPTY |+ ("a",1) |+ ("b",2)) |+ ("a" , 3)
Proof
fsrw_tac [FMAP_ss] [finite_mapTheory.FUPDATE_COMMUTES]
(* Alternative proof using conv directly:

CONV_TAC (fupdate_subterm_NORMALISE_CONV) >>
fs [finite_mapTheory.FUPDATE_COMMUTES]

*)
QED

*)

(* Obtains the list of assumptions for a reduction clause-theorem *)
fun get_clause_assums thm =
 (strip_conj o fst o dest_imp o concl o SPEC_ALL) thm
;

(* Finds the rule with name clause_name_str in a Ott-exported reduction rules-theorem  *)
fun find_clause thm clause_name_str =
 let
  val clause_name_str_tm = stringSyntax.fromMLstring clause_name_str
  val conj_thms = CONJUNCTS thm
 in
  List.find (
   (fn assums => isSome (List.find
    (fn tm =>
     if is_clause_name tm
     then term_eq (dest_clause_name tm) clause_name_str_tm
     else false)
    assums)
   ) o get_clause_assums) conj_thms
 end
;
(* find_clause, hard-coded for the expression reduction theorem *)
val find_clause_e_red = find_clause e_red_rules
(* find_clause, hard-coded for the statement reduction theorem *)
val find_clause_stmt_red = find_clause stmt_red_rules
(* find_clause, hard-coded for the frame reduction theorem *)
val find_clause_frames_red = find_clause frames_red_rules

end
