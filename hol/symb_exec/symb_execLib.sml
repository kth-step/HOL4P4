structure symb_execLib :> symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open hurdUtils listTheory listSyntax;

open symb_execTheory symb_execSyntax;

datatype path_tree = empty | node of int * thm * (path_tree list);

val ERR = mk_HOL_ERR "symb_exec"

(* TODO: Optimize? *)
fun insert_nodes' empty (at_id, thm, new_nodes) _ = NONE
  | insert_nodes' (node (id, thm, nodes)) (at_id, new_thm, new_nodes) nodes_temp = 
   if at_id = id
   then
    if null nodes
    then SOME (node (id, new_thm, new_nodes))
    else NONE (* Erroneously trying to insert new nodes in occupied position *)
   else
    if null nodes
    then NONE (* Reached end of search *)
    else
     case insert_nodes' (hd nodes) (at_id, new_thm, new_nodes) [] of
       SOME new_node =>
      SOME (node (id, thm, nodes_temp@(new_node::(tl nodes))))
     | NONE =>
      insert_nodes' (node (id, thm, tl nodes)) (at_id, new_thm, new_nodes) (nodes_temp@[hd nodes]);

fun insert_nodes path_tree (at_id, new_thm, new_nodes) =
 case insert_nodes' path_tree (at_id, new_thm, new_nodes) [] of
   SOME new_path_tree =>
  new_path_tree
 | NONE =>
  raise (ERR "insert_nodes" "Inserting new path node at unknown or occupied position ");

(* TODO: Rename "branch condition" to something else? Is this terminology OK? *)
local
(* TODO: Factor out *)
fun p4_conv path_cond_tm tm =
 let
  val thm = ((PURE_REWRITE_CONV [symb_conj_def]) THENC (CHANGED_CONV blastLib.BBLAST_CONV)) tm
   handle HOL_ERR msg => (SPECL [path_cond_tm, snd $ dest_symb_conj tm] add_assum)
 in
  if Feq $ rhs $ concl thm then SOME thm else SOME (SPECL [path_cond_tm, snd $ dest_symb_conj tm] add_assum)
 end
(* Generic symbolic execution
 * This has four language-specific parameters:
 *
 * lang_regular_step (thm * thm -> thm): Takes one regular step in the language lang
 *   (takes a path condition in theorem form and a step theorem and transforms it into
 *    a new step theorem)
 *
 * lang_init_step_thm (thm): Step theorem for zero steps
 *
 * lang_should_branch (thm -> (term list * thm) option): Decides whether to branch
 * by looking at the current step theorem. Returns NONE if branching should not
 * happen, and a list of different branch conditions (used to update the path conditions)
 * and a disjunction theorem stating that the disjunction of the branch conditions holds.

 * lang_is_finished (thm -> bool): Decides whether symbolic execution should continue
 * on this path by looking at the current step theorem.
 *
 * Note that branching consumes one step of (SML function) fuel *)
fun symb_exec' lang_funs npaths path_tree [] finished_list = (path_tree, finished_list)
  | symb_exec' lang_funs npaths path_tree ((path_id, path_cond, step_thm, 0, nobranch_flag)::t) finished_list =
   symb_exec' lang_funs npaths path_tree t (finished_list@[(path_id, path_cond, step_thm)])
  | symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) npaths
               path_tree ((path_id, path_cond, step_thm, fuel, nobranch_flag)::t) finished_list =
   (* Check if we should branch or take regular step
    * lang_should_branch can be made an argument: it takes the current step theorem
    * and returns a term with the branch condition, with which you can split the
    * path condition *)
   (case (if nobranch_flag then NONE else lang_should_branch step_thm) of
     SOME disj_thm =>
(* Debug:
 val SOME disj_thm = lang_should_branch step_thm
*)
     (* Branch + prune *)
     let

(* Debug:

val path_cond = ASSUME “c <=> T”;
val disj_thm = prove(“disj_list [a; b; ~c]”, cheat);

*)
      (* TODO: This relies on the fact that PURE_REWRITE_RULE retains path
       * condition T as a conjunct. Is
       * this a hack? Should symb_branch_cases be used from the get-go?
       * Could introduce definitions/abbreviations instead. *)

      (* 1. Get disj_list with path condition conjoined *)
      val path_cond_tm = concl path_cond
      val path_disj_thm = CONJ path_cond disj_thm;
      val disj_list_rewr_thm = PURE_REWRITE_RULE [MAP, BETA_THM] (SPECL [path_cond_tm, dest_disj_list' $ concl disj_thm] disj_list_CONJ);
      val path_disj_thm2 = PURE_REWRITE_RULE [disj_list_rewr_thm] path_disj_thm;

      (* 2. Get theorems stating contradictions - or other simplifications - among
       * any of the disjuncts *)
      (* Note: if the term is unchanged, the path condition must be the first conjunct *)
      val F_thm_list = foldl (fn (tm, rewrs) => case p4_conv path_cond_tm tm of SOME thm => (thm::rewrs) | NONE => rewrs) [] (dest_disj_list $ concl path_disj_thm2);
      val path_disj_thm3 = PURE_REWRITE_RULE F_thm_list path_disj_thm2;

      (* 3. Remove F-entries from the disj_list *)
      val path_disj_thm4 =
       PURE_REWRITE_RULE [GSYM disj_list_symb_disj_REWR, disj_list_symb_disj_REWR_extra] $
       PURE_REWRITE_RULE [disj_list_symb_disj_REWR, symb_disj_F] path_disj_thm3;
      val new_path_conds = dest_disj_list $ concl $ PURE_REWRITE_RULE [symb_conj_def] path_disj_thm4;

      (* 4. Remove the path condition as conjunct from the list entries, keeping it as an assumption *)
      (* TODO: Here, path condition can be simplified. But then it also becomes harder to
       * rewrite with... *)
      (* TODO: Don't translate back and forth to symb_true here, do once and for all and at end *)
      val path_disj_thm4' = PURE_REWRITE_RULE [GSYM symb_true_def] (DISCH_ALL path_disj_thm4)

      val path_disj_thm5 = SIMP_RULE ((pure_ss++boolSimps.BOOL_ss++boolSimps.CONG_ss)-*["NOT_CLAUSES"]) [CONJUNCT2 NOT_CLAUSES, symb_conj_case, EQ_REFL] path_disj_thm4';

      val path_disj_thm6 = PURE_REWRITE_RULE [GSYM symb_branch_cases_def, symb_conj_def, AND_CLAUSES] path_disj_thm5
      val path_disj_thm7 = PURE_REWRITE_RULE [symb_true_def] path_disj_thm6
 
      val new_branch_cond_tms = fst $ dest_list $ snd $ dest_symb_branch_cases $ concl path_disj_thm7

      (* TODO: OPTIMIZE: Check if branch results in just one new path - then we don't need to add
       * a new node to the tree, just replace data in the existing one *)
      val (npaths', new_path_elems) =
       foldl
        (fn ((path_cond, branch_cond), (curr_path_id, curr_path_cond_list)) =>
	 (curr_path_id+1,
	  (* TODO: OPTIMIZE: Cons instead of append? will reverse order *)
          (* New path IDs are assigned in increments of 1 from the existing max (npaths) *)
	  (curr_path_cond_list@[(curr_path_id+1,
                                 (* The path condition, as a theorem *)
				 path_cond,
                                 (* The current step theorem, rewritten using the path condition as
                                  * a theorem (will add path condition as a premise) *)
                                 (* Old: *)
                                 (* DISCH_CONJUNCTS_ALL $ REWRITE_RULE [path_cond] step_thm *)
                                 (* New, a bit of a silly hack: *)
                                 PURE_REWRITE_RULE [SPEC branch_cond AND_IMP_INTRO_SYM] $ DISCH_CONJUNCTS_ALL $ ADD_ASSUM branch_cond step_thm,
                                 (* Branching consumes 1 fuel *)
				 fuel-1,
                                 (* This flags tells the symbolic execution to not branch this
                                  * path on next encounter *)
				 true)])))
        (npaths, [])
        (zip (map ASSUME new_path_conds) new_branch_cond_tms)

      (* The new path tree nodes are mostly placeholders until further branches take place,
       * but they do already store the path ID (first element) *)
      (* TODO: Using TRUTH as placeholder - use option type in path_tree instead? *)
      val new_path_nodes = map (fn (a,b,c,d,e) => node (a, TRUTH, [])) new_path_elems

      (* This updates the node holding the path which was branched: it now gets assigned a
       * path disjunction theorem *)
      val new_path_tree = insert_nodes path_tree (path_id, path_disj_thm7, new_path_nodes)
     in
(*
val npaths = npaths'
val path_tree = new_path_tree

val (path_id, path_cond, step_thm, fuel) = hd new_path_elems
val nobranch_flag = true
*)
      symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) npaths'
                  new_path_tree (t@new_path_elems) finished_list
     end
    | NONE =>
     (* Do not branch - compute one regular step *)
     let
      val next_step_thm =
       lang_regular_step (path_cond, step_thm)
     in
      if lang_is_finished next_step_thm
      then
       symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) npaths
                  path_tree t (finished_list@[(path_id, path_cond, next_step_thm)])
      else
       symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) npaths
                  path_tree (t@[(path_id, path_cond, next_step_thm, fuel-1, false)]) finished_list
     end)
in
fun symb_exec (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) path_cond fuel =
 symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) 1
            (node (1, TRUTH, [])) [(1, path_cond, lang_init_step_thm, fuel, false)] []
end;

end
