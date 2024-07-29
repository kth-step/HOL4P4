structure symb_execLib :> symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open hurdUtils listTheory listSyntax;

open symb_execTheory symb_execSyntax;

(* May give errors, don't fret about it *)
open Thread Mutex ConditionVar ThreadLib;
(* TODO: Try using "synchronized" from Multithreading.sml instead of "protect"
 * from ThreadLib.sml *)

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
 * with e1 ... en as free variables.
 * *)
fun convert_exists branch_cond step_thm =
 (* Don't remove the boolSyntax prefix: conflict between boolSyntax and listSyntax *)
 if boolSyntax.is_exists branch_cond
 then
  let
   val branch_cond' = snd $ strip_exists branch_cond
  in
   (SPEC branch_cond' (MATCH_MP IMP_ADD_CONJ step_thm))
  end
 else (PURE_REWRITE_RULE [SPEC branch_cond AND_IMP_INTRO_SYM] $ DISCH_CONJUNCTS_ALL $ ADD_ASSUM branch_cond step_thm)
;

(* Takes a path condition in the shape of a term and
 * changes the last conjunct to one without existentially
 * quantified variables (if it has any). *)
fun convert_exists_path_cond path_cond_tm =
 let
  val conjs = strip_conj path_cond_tm
  val last_conj = last conjs
 in
  if boolSyntax.is_exists last_conj
  then
   let
    val last_conj' = snd $ strip_exists last_conj
   in
    list_mk_conj (rev (last_conj'::(tl $ rev conjs)))
   end
  else path_cond_tm
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

fun update_path_tree debug_flag (npaths, path_tree, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel) =
 let
  val time_start = Time.now();

  val _ = dbg_print debug_flag
   (String.concat ["\n\nUpdating path tree...\n\n"])

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
                             (convert_exists branch_cond step_thm),
			     (* Branching consumes 1 fuel *)
			     fuel-1,
			     (* This flags tells the symbolic execution to not branch this
			      * path on next encounter *)
			     true)])))
    (npaths, [])
    (zip fv_indices (zip (map (ASSUME o convert_exists_path_cond) new_path_conds) new_branch_cond_tms))

  (* The new path tree nodes are mostly placeholders until further branches take place,
   * but they do already store the path ID (first element) *)
  (* TODO: Using TRUTH as placeholder - use option type in path_tree instead? *)
  val new_path_nodes = map (fn (a,b,c,d,e,f) => node (a, TRUTH, [])) new_path_elems

  (* This updates the node holding the path which was branched: it now gets assigned a
   * path disjunction theorem *)
  val new_path_tree = insert_nodes path_tree (path_id, path_disj_thm7, new_path_nodes)

  val _ = dbg_print debug_flag (String.concat ["Finished path_tree update in: ",
				(LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				" ms\n"])

 in
  (npaths', new_path_tree, new_path_elems)
 end
;

fun symb_branch debug_flag disj_thm path_cond =
 let
  val time_start = Time.now();

 (* Debug:

 val path_cond = ASSUME “c <=> T”;
 val disj_thm = prove(“disj_list [a; b; ~c]”, cheat);

 val path_cond = ASSUME “a /\ T /\ c”;
 val disj_thm = prove(“c ==> (b1 \/ b2)”, cheat);
 val test = REWRITE_RULE [path_cond] disj_thm;

 *)
  (* TODO: This relies on the fact that PURE_REWRITE_RULE retains path
   * condition T as a conjunct. Is
   * this a hack? Should symb_branch_cases be used from the get-go?
   * Could introduce definitions/abbreviations instead. *)

  (* 1. Get disj_list with path condition conjoined *)
  val path_cond_tm = concl path_cond
  (* This is used in the situation when disj_thm is in the shape A ==> B1 \/ ... \/ Bn, and A can be
   * resolved by the path condition. *)
  val disj_thm' = if is_imp $ concl disj_thm
                  then REWRITE_RULE [path_cond] disj_thm
                  else disj_thm
  val _ = if is_imp $ concl disj_thm'
          then raise (ERR "symb_branch" "Antecedent of disj_thm could not be proved from path condition")
          else ()
  val path_disj_thm = CONJ path_cond disj_thm';

  val disj_list_rewr_thm = PURE_REWRITE_RULE [MAP, BETA_THM] (SPECL [path_cond_tm, dest_disj_list' $ concl disj_thm'] disj_list_CONJ);
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

  val res =
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

  val _ = dbg_print debug_flag (String.concat ["Finished symbolic branch in: ",
				(LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				" ms\n"])
 in
  res
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
     let
      val _ = dbg_print debug_flag
       (String.concat ["\n\nPerforming symbolic branch...\n\n",
		       (* "from step_thm:\n", (term_to_string $ concl step_thm), *)
		       "using disj_thm:\n", (term_to_string $ concl disj_thm),
		       "\n and path condition \n", (term_to_string $ concl path_cond), "\n\n"])
     in
      (case symb_branch debug_flag disj_thm path_cond of
(*
 val SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms) = symb_branch debug_flag disj_thm path_cond
*)
	 (* TODO: Better names *)
	(* Branch + prune *)
	 SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms) =>
	let
	 val (npaths', new_path_tree, new_path_elems) = update_path_tree debug_flag (npaths, path_tree, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel)
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
      end
     | NONE =>
      (* Do not branch - compute one regular step *)
      let

       (* DEBUG *)
       val time_start = Time.now();

       val next_step_thm =
	lang_regular_step nobranch_flag step_thm
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
 case get_job () of
   SOME (path_id, fv_index, path_cond, step_thm, fuel, nobranch_flag) =>
  (case (if nobranch_flag then NONE else (lang_should_branch (fv_index, step_thm))) of
    SOME (disj_thm, fv_indices) =>
   (case symb_branch debug_flag disj_thm path_cond of
      (* TODO: Better names *)
     (* Branch + prune *)
      SOME (new_path_conds, path_disj_thm7, new_branch_cond_tms) =>
     (update_shared_state debug_flag (new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel);
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
     lang_regular_step nobranch_flag step_thm
      (* TODO: broadcastInterrupt doesn't seem to work properly *)
      handle Interrupt => ((* broadcastInterrupt(); *) print "Interrupt exception when running lang_regular_step!\n"; raise Interrupt)
      handle exc => ((* broadcastInterrupt(); *) print "Exception when running lang_regular_step!\n"; raise exc)

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
 (* TODO: Silly, but works against silent exceptions *)
 handle Interrupt => ((* broadcastInterrupt(); *) print "Interrupt exception!\n"; raise Interrupt)
 handle exc => ((* broadcastInterrupt(); *)
                print (String.concat ["Exception raised on path ID ", (Int.toString path_id), "\n",
                       "with ", (Int.toString fuel), " fuel remaining,\n",
                       "free variable index ", (Int.toString fv_index), ",\n",
                       "and step_thm\n", (term_to_string $ concl step_thm), "\n"]); raise exc))
 | NONE => ()
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
   protect mutex_exec (fn () =>
    (let
      val queue = (!work_queue)
     in
      if not (null queue)
      then
       let
        val res = (hd queue)
       in
        (work_queue := tl queue; SOME res)
       end
      else
       (nthreads_ref := !nthreads_ref - 1;
	(if !nthreads_ref = 0
	 then (signal all_done; NONE)
	 else NONE))
     end)) ();

  fun append_jobs jobs =
   protect mutex_exec (fn jobs' => (work_queue := ((!work_queue)@jobs'))) jobs;

  fun update_shared_state debug_flag (new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel) =
   protect mutex_exec (fn () =>
    (let
      val (npaths', new_path_tree, new_path_elems) = update_path_tree debug_flag (!npaths_ref, !path_tree_ref, new_path_conds, path_disj_thm7, new_branch_cond_tms, fv_indices) (path_id, step_thm, fuel);
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

  (* TODO: Hack, enables this thread to shut down *)
  val _ = setAttributes [EnableBroadcastInterrupt true]
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

(****************************)
(* Generic helper functions *)
(****************************)

(* These generic functions help in implementing language-specific symbolic execution machinery. *)

(* Proves that postcond holds for the final state of a step_thm *)
fun prove_postcond rewr_thms postcond step_thm =
 let
  val prel_res_thm = HO_MATCH_MP symb_exec_add_postcond step_thm
  val (hypo, step_tm) = dest_imp $ concl step_thm
  val res_state_tm = optionSyntax.dest_some $ snd $ dest_eq step_tm
  (* TODO: OPTIMIZE: srw_ss??? *)
  val postcond_thm = EQT_ELIM $ (SIMP_CONV ((srw_ss())++bitstringLib.BITSTRING_GROUND_ss++boolSimps.LET_ss) rewr_thms) $ mk_imp (hypo, mk_comb (postcond, res_state_tm))
 in
  MATCH_MP prel_res_thm postcond_thm
 end
;

(* DEBUG
val step_thms = map #3 path_cond_step_list;

(* basic: Index 24, 32, 52, 67 are interesting *)
val h = el 24 step_thms
val h = el 32 step_thms
val h = el 52 step_thms
val h = el 67 step_thms

val step_thm = h
val rewr_thms = p4_prove_postcond_rewr_thms
*)
fun prove_postconds_debug' rewr_thms postcond []     _ = []
  | prove_postconds_debug' rewr_thms postcond (h::t) n =
 let
  val res = prove_postcond rewr_thms postcond h
   handle exc => (print (("Error when proving postcondition for n-step theorem at 0-index "^(Int.toString n))^"\n"); raise exc)
 in
  (res::(prove_postconds_debug' rewr_thms postcond t (n + 1)))
 end
;
fun prove_postconds debug_flag rewr_thms postcond path_cond_step_list =
 if debug_flag
 then
  let
   val (l', l'') = unzip $ map (fn (a,b,c) => (a, c)) path_cond_step_list
  in
   zip l' (prove_postconds_debug' rewr_thms postcond l'' 0)
  end
 else map (fn (a,b,c) => (a, prove_postcond rewr_thms postcond c)) path_cond_step_list
;

end
