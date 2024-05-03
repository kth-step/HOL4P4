structure symb_execLib :> symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open hurdUtils listTheory listSyntax;

open symb_execTheory symb_execSyntax;

(* May give errors, don't fret about it *)
open Thread Mutex ConditionVar ThreadLib;

datatype path_tree = empty | node of int * thm * (path_tree list);

val ERR = mk_HOL_ERR "symb_exec"

fun dbg_print debug_flag string =
 if debug_flag
 then print string
 else ()
;

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

fun count_leaves (node (id, thm, nodes)) =
 if null nodes
 then 1
 else foldl (fn (el, n) => (count_leaves el) + n) 0 nodes
  | count_leaves empty = 0;

(* Takes a step theorem Q and a branch condition of the shape
 *   (?e1 ... en. P (e1 ... en))
 * (possibly with n=0) and converts it to the new step theorem
 *   P (e1 ... en) ==> Q
 * with e1 ... en as free variables, also returns the new branch condition
 * tupled with this result.
 * *)
fun convert_exists branch_cond step_thm =
 let
  val thm = DISCH_CONJUNCTS_ALL $ ADD_ASSUM branch_cond step_thm
  val (ante, cons) = dest_imp $ concl thm
 in
  (* Don't remove the boolSyntax prefix *)
  if boolSyntax.is_exists ante
  then
   let
    val (vars, ante') = strip_exists ante
    val tm' = mk_imp (ante', cons)
    (* DEBUG
    val _ = print "Attempting proof in convert_exists...\n"
    *)
   in
    (* TODO: Why doesn't SIMP_TAC bool_ss [step_thm] work here? investigate... *)
    (prove(tm', fs [step_thm]), ante')
(*
     handle exc => (raise (ERR "convert_exists" "Failed to prove conversion of existential quantifiers in step theorem"))
*)
     handle exc => (print (String.concat ["branch_cond: ", term_to_string branch_cond, "\n",
                                          "step_thm: ", term_to_string $ concl step_thm, "\n"]);
                    raise (ERR "convert_exists" "Failed to prove conversion of existential quantifiers in step theorem"))
   end
  else (thm, branch_cond)
 end
;

(* TODO: Rename "branch condition" to something else? Is this terminology OK? *)
(* TODO: Can this be considered to be P4-dependent or not? *)
fun p4_conv path_cond_tm tm =
 let
  val thm = ((PURE_REWRITE_CONV [symb_conj_def]) THENC (CHANGED_CONV blastLib.BBLAST_CONV)) tm
   handle HOL_ERR msg => (SPECL [path_cond_tm, snd $ dest_symb_conj tm] add_assum)
 in
  if Feq $ rhs $ concl thm then SOME thm else SOME (SPECL [path_cond_tm, snd $ dest_symb_conj tm] add_assum)
 end
;

fun update_path_tree (npaths, path_tree, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel) =
 let
  (* TODO: OPTIMIZE: Check if branch results in just one new path - then we don't need to add
   * a new node to the tree, just replace data in the existing one *)
  val (npaths', new_path_elems) =
   foldl
    (fn ((fv_index, (path_cond, branch_cond)), (curr_path_id, curr_path_cond_list)) =>
     (curr_path_id+1,
      (* New path IDs are assigned in increments of 1 from the existing max (npaths) *)
      (curr_path_cond_list@[(curr_path_id+1,
			     (* Current index for free variables introduced by the symbolic execution *)
                             fv_index,
			     (* The path condition, as a theorem *)
			     path_cond,
			     (* The current step theorem, rewritten using the path condition as
			      * a theorem (will add path condition as a premise) *)
			     (* Old: *)
			     (* DISCH_CONJUNCTS_ALL $ REWRITE_RULE [path_cond] step_thm *)
			     (* New, a bit of a silly hack: *)
                             (fn (thm, tm) => PURE_REWRITE_RULE [SPEC tm AND_IMP_INTRO_SYM] thm) $ convert_exists branch_cond step_thm,
			     (* Branching consumes 1 fuel *)
			     fuel-1,
			     (* This flags tells the symbolic execution to not branch this
			      * path on next encounter *)
			     true)])))
    (npaths, [])
    (zip fv_indices (zip (map ASSUME new_path_conds) new_branch_cond_tms))

  (* The new path tree nodes are mostly placeholders until further branches take place,
   * but they do already store the path ID (first element) *)
  (* TODO: Using TRUTH as placeholder - use option type in path_tree instead? *)
  val new_path_nodes = map (fn (a,b,c,d,e,f) => node (a, TRUTH, [])) new_path_elems

  (* This updates the node holding the path which was branched: it now gets assigned a
   * path disjunction theorem *)
  val new_path_tree = insert_nodes path_tree (path_id, path_disj_thm7, new_path_nodes)

 in
  (npaths', new_path_tree, new_path_elems)
 end
;

fun symb_branch disj_thm path_cond =
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
  val path_disj_thm2 = PURE_REWRITE_RULE [MAP, BETA_THM, disj_list_rewr_thm] path_disj_thm;

  (* 2. Get theorems stating contradictions - or other simplifications - among
   * any of the disjuncts *)
  (* Note: if the term is unchanged, the path condition must be the first conjunct *)
  val F_thm_list = foldl (fn (tm, rewrs) => case p4_conv path_cond_tm tm of SOME thm => (thm::rewrs) | NONE => rewrs) [] (dest_disj_list $ concl path_disj_thm2);
  val path_disj_thm3 = PURE_REWRITE_RULE F_thm_list path_disj_thm2;

  (* 3. Remove F-entries from the disj_list *)
  val path_disj_thm4 =
   PURE_REWRITE_RULE [GSYM disj_list_symb_disj_REWR, disj_list_symb_disj_REWR_extra] $
   PURE_REWRITE_RULE [disj_list_symb_disj_REWR, symb_disj_F] path_disj_thm3;
  (* TODO: Discover no new paths already here? *)
  val new_path_conds =
   let
    val disj_list = concl $ PURE_REWRITE_RULE [symb_conj_def] path_disj_thm4;
   in
    if is_disj_list disj_list
    then dest_disj_list disj_list
    else [disj_list]
   end

  (* 4. Remove the path condition as conjunct from the list entries, keeping it as an assumption *)
  (* TODO: Here, path condition can be simplified. But then it also becomes harder to
   * rewrite with... *)
  (* TODO: Don't translate back and forth to symb_true here, do once and for all and at end *)
  val path_disj_thm4' = PURE_REWRITE_RULE [GSYM symb_true_def] (DISCH_ALL path_disj_thm4)

  val path_disj_thm5 = SIMP_RULE ((pure_ss++boolSimps.BOOL_ss++boolSimps.CONG_ss)-*["NOT_CLAUSES"]) [CONJUNCT2 NOT_CLAUSES, symb_conj_case, EQ_REFL] path_disj_thm4';
 in
  if Teq $ concl path_disj_thm5
  then NONE
  else
   let
    val path_disj_thm6 = PURE_REWRITE_RULE [GSYM symb_branch_cases_def, symb_conj_def, AND_CLAUSES] path_disj_thm5
    val path_disj_thm7 = PURE_REWRITE_RULE [symb_true_def] path_disj_thm6

    val new_branch_cond_tms = fst $ dest_list $ snd $ dest_symb_branch_cases $ concl path_disj_thm7
   in
    SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms)
   end
 end
;


local
 (* Generic symbolic execution
  * This has four language-specific parameters:
  *
  * lang_regular_step (thm -> thm): Takes one regular step in the language lang
  *   (takes a step theorem and transforms it into a new step theorem)
  *
  * lang_init_step_thm (thm): Step theorem for zero steps
  *
  * lang_should_branch (thm -> (term list * thm) option): Decides whether to branch
  * by looking at the current step theorem. Returns NONE if branching should not
  * happen, and a list of different branch conditions (used to update the path conditions)
  * and a disjunction theorem stating that the disjunction of the branch conditions holds.
  *
  * lang_is_finished (thm -> bool): Decides whether symbolic execution should continue
  * on this path by looking at the current step theorem.
  *
  * Note that branching consumes one step of (SML function) fuel *)
 fun symb_exec' lang_funs (npaths, path_tree, [], finished_list) = (path_tree, finished_list)
   | symb_exec' lang_funs (npaths, path_tree, ((path_id, fv_index, path_cond, step_thm, 0, nobranch_flag)::t), finished_list) =
    symb_exec' lang_funs (npaths, path_tree, t, (finished_list@[(path_id, path_cond, step_thm)]))
   | symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (npaths,
		path_tree, ((path_id, fv_index, path_cond, step_thm, fuel, nobranch_flag)::t), finished_list) =
    (* Check if we should branch or take regular step
     * lang_should_branch can be made an argument: it takes the current step theorem
     * and returns a term with the branch condition, with which you can split the
     * path condition *)
    (case (if nobranch_flag then NONE else lang_should_branch (fv_index, step_thm)) of
      SOME (disj_thm, fv_indices) =>
 (* Debug:
  val SOME (disj_thm, fv_indices) = lang_should_branch (fv_index, step_thm)
 *)
     (case symb_branch disj_thm path_cond of
        (* TODO: Better names *)
       (* Branch + prune *)
        SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms) =>
       let
	val (npaths', new_path_tree, new_path_elems) = update_path_tree (npaths, path_tree, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel)
       in
  (*
  val npaths = npaths'
  val path_tree = new_path_tree

  val (path_id, path_cond, step_thm, fuel) = hd new_path_elems
  val nobranch_flag = true
  *)
	symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (npaths',
		    new_path_tree, (t@new_path_elems), finished_list)
       end
       (* No new paths *)
      | NONE =>
       symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (npaths, path_tree, (t@[(path_id, fv_index, path_cond, step_thm, fuel-1, true)]), finished_list))
     | NONE =>
      (* Do not branch - compute one regular step *)
      let

       (* DEBUG *)
       val time_start = Time.now();

       val next_step_thm =
	lang_regular_step step_thm
       val _ = dbg_print debug_flag
	(String.concat ["Finished regular symbolic execution step of path ID ",
			(Int.toString path_id), " in ",
			(LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
			" ms, fuel remaining: ",
			(Int.toString (fuel - 1)), "\n"])
      in
       if lang_is_finished next_step_thm
       then
	symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (npaths,
		   path_tree, t, (finished_list@[(path_id, path_cond, next_step_thm)]))
       else
	symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (npaths,
		   path_tree, (t@[(path_id, fv_index, path_cond, next_step_thm, fuel-1, false)]), finished_list)
      end)
in
 fun symb_exec (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) path_cond fuel =
  symb_exec' (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) (1,
	     (node (1, TRUTH, [])), [(1, 0, path_cond, lang_init_step_thm, fuel, false)], [])
end;

fun symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state) =
 let
  val (npaths, path_tree, (path_id, fv_index, path_cond, step_thm, fuel, nobranch_flag)) = get_job ()
 in
  case (if nobranch_flag then NONE else (lang_should_branch (fv_index, step_thm))) of
    SOME (disj_thm, fv_indices) =>
    (* symb_branch should return not a new path tree, but the nodes which should be inserted.
     * get_job should not return npaths and path_tree. There should then be a new method which updates
     * path_tree and npaths based on the new nodes which should be added (basically: safe version of insert_nodes). *)
   (case symb_branch disj_thm path_cond of
      (* TODO: Better names *)
     (* Branch + prune *)
      SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms) =>
     (update_shared_state (new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel);
      register_new_worker_n (fn () => (symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state))) ((length (new_path_conds))-1);
      symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state))
     (* No new paths *)
    | NONE =>
     (append_jobs [(path_id, fv_index, path_cond, step_thm, fuel-1, true)];
      symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state)))
  | NONE =>
   let
    (* DEBUG *)
    val time_start = Time.now();

    val next_step_thm =
     lang_regular_step step_thm

    val _ = dbg_print debug_flag
     (String.concat ["Finished regular symbolic execution step of path ID ",
		     (Int.toString path_id), " in ",
		     (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
		     " ms, fuel remaining: ",
		     (Int.toString (fuel - 1)), "\n"])
    val fuel' = fuel-1
   in
    (* First, check if the current job is finished (language-dependent function lang_is_finished),
     * then finish it (concurrency function finish_job) *)
    if lang_is_finished next_step_thm orelse fuel' = 0
    then
     if finish_job (path_id, path_cond, next_step_thm)
     then ()
     else symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state)
    else (append_jobs [(path_id, fv_index, path_cond, next_step_thm, fuel', false)]; symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state))
   end
 end
;

fun symb_exec_conc (debug_flag, lang_regular_step, lang_init_step_thm, lang_should_branch, lang_is_finished) path_cond fuel nthreads_max =
 let
  val work_queue = ref [(1, 0, path_cond, lang_init_step_thm, fuel, false)]
  val npaths_ref = ref 1
  val path_tree_ref = ref (node (1, TRUTH, []))
  val done_list = ref ([]:(int * thm * thm) list)

  val nthreads_ref = ref 0
  val all_done = conditionVar()
  val mutex_exec = mutex()

  fun get_job () =
   protect mutex_exec (fn () => (let val res = (!npaths_ref, !path_tree_ref, hd (!work_queue)) in work_queue := tl (!work_queue); res end)) ();

  fun append_jobs jobs =
   protect mutex_exec (fn jobs' => (work_queue := ((!work_queue)@jobs'))) jobs;

  fun update_shared_state (new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel) =
   protect mutex_exec (fn () =>
    (let
      val (npaths', new_path_tree, new_path_elems) = update_path_tree (!npaths_ref, !path_tree_ref, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel);
      val _ = (npaths_ref := npaths');
      val _ = (path_tree_ref := new_path_tree);
      val _ = (work_queue := ((!work_queue)@new_path_elems));
     in
      ()
     end)) ();

  fun finish_job job =
   protect mutex_exec
    (fn job' =>
     (done_list := ((!done_list)@[job']);
      if null (!work_queue)
      then
       (nthreads_ref := !nthreads_ref - 1;
	(if !nthreads_ref = 0
	 then (signal all_done; true)
	 else true))
      else false)) job;

  fun register_new_worker (work_fun:unit -> unit) =
   protect mutex_exec (fn () => (if !nthreads_ref < nthreads_max then let val _ = (nthreads_ref := !nthreads_ref + 1); val _ = (fork (work_fun, [EnableBroadcastInterrupt true])) in () end else ())) ();

  (* TODO: Slightly inefficient since it always loops through all iterations, but should work.
   * Make register_worker return a success bool also *)
  fun register_new_worker_n (work_fun:unit -> unit) 0 = ()
    | register_new_worker_n work_fun n = 
   let
    val _ = register_new_worker work_fun
   in
    register_new_worker_n (work_fun:unit -> unit) (n-1)
   end;

  val time_start = Time.now();
  val _ = register_new_worker (fn () => symb_exec_conc' (debug_flag, lang_regular_step, lang_should_branch, lang_is_finished) (register_new_worker_n, get_job, append_jobs, finish_job, update_shared_state))
 in
   (wait (all_done, mutex_exec);
    (* TODO: Safe? *)
    (!path_tree_ref, !done_list)
(*
    print (String.concat ["Result: ",
                   String.concat $ map (fn el => (el^" ")) (map (term_to_string o concl o #3) (!done_list)),
                   "\nTime: ",
                   (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
                   " ms\n"])
*)
)
 end
;

end
