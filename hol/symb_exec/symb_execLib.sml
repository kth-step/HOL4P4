structure symb_execLib :> symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open hurdUtils;

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
      SOME (node (id, new_thm, nodes_temp@(new_node::(tl nodes))))
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
(* Symbolic execution with branching on if-then-else
 * Width-first scheduling (positive case first) of execution
 * Note that branching consumes one step of (SML function) fuel
 * Here, the static ctxt and the dynamic path condition have been merged.
 * Currently, the path condition is stripped down as much as possible from p4-specific stuff
 * (another design priority could be legibility and keeping the connection to the P4 constructs). *)
fun symb_exec' lang_funs npaths path_tree [] finished_list = (path_tree, finished_list)
  | symb_exec' lang_funs npaths path_tree ((path_id, path_cond, step_thm, 0)::t) finished_list =
   symb_exec' lang_funs npaths path_tree t (finished_list@[(path_id, path_cond, step_thm)])
  | symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) npaths
               path_tree ((path_id, path_cond, step_thm, fuel)::t) finished_list =
   (* Check if we should branch or take regular step
    * lang_should_branch can be made an argument: it takes the current step theorem
    * and returns a term with the branch condition, with which you can split the
    * path condition *)
   (case lang_should_branch step_thm of
     SOME (branch_cond_list, path_disj_thm) =>
     (* Branch + prune *)
     let
      (* Get all path conditions in the shape of Cn /\ P ==> P /\ Cn *)
      (* TODO: Why this tautological shape? Why store path_cond as a theorem and not a term? *)
      val new_path_conds = map (CONJ path_cond o ASSUME) branch_cond_list

      (* Simplify: some path conditions will now take the shape Cn /\ P ==> Cn /\ P <=> F *)
      (* TODO: This rule might also be a language parameter *)
      val new_path_conds' = map (SIMP_RULE std_ss []) new_path_conds

      (* TODO: OPTIMIZE: Check if branch results in just one new path - then we don't need to add
       * a new node to the tree, just replace data in the existing one *)
      val (npaths', new_path_elems) =
       foldl
        (fn (path_cond, (curr_path_id, curr_path_cond_list)) =>
	 if Feq $ concl path_cond 
	 then (curr_path_id, curr_path_cond_list)
	 else (curr_path_id+1,
               (* TODO: OPTIMIZE: Cons instead of append? will reverse order *)
               (curr_path_cond_list@[(curr_path_id+1,
                                      path_cond,
                                      DISCH_CONJUNCTS_ALL $ REWRITE_RULE [path_cond] step_thm,
                                      fuel-1)])))
        (npaths, [])
        new_path_conds'

      (* TODO: Using TRUTH as a placeholder - use thm option type in path_tree instead? *)
      val new_path_nodes = map (fn (a,b,c,d) => node (a, TRUTH, [])) new_path_elems

      val new_path_tree = insert_nodes path_tree (path_id, path_disj_thm, new_path_nodes)
     in
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
                  path_tree (t@[(path_id, path_cond, next_step_thm, fuel-1)]) finished_list
     end)
in
fun symb_exec (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) path_cond fuel =
 symb_exec' (lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) 1
            (node (1, TRUTH, [])) [(1, path_cond, lang_init_step_thm, fuel)] []
end;

end
