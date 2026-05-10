open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;
open bdd_genTheory;

val _ = new_theory "bdd_gen_new";


(*

(* new BDD types *)



Datatype:
  id = id_termn  'a
       | id_non_termn (string option)
End


Type label_id = “:(num , ('b id # num)) alist”;
Type label_content = “:(num , 'a) alist”;

Type BDD_sep = “:num # edges # 'b label_id # 'a label_content”
Type BDD_mini = “:num # edges # 'b label_id”



(* get labels identified by the leafs *)


(* gets the label only for non terminal leaf*)
Definition getLabels_new_def:
  (getLabels_new (labels_id: 'b label_id) (labels_content: 'a label_content) [] = SOME []) ∧
  (getLabels_new (labels_id: 'b label_id) (labels_content: 'a label_content) (n::leaves) =
   case (getLabels_new labels_id labels_content leaves) of
   | SOME l =>
       (
       case (ALOOKUP labels_id n) of
       | NONE => NONE
       | SOME (id_non_termn NONE, m) => (
         case (ALOOKUP labels_content m) of
         | NONE => NONE
         | SOME (content) => SOME ((n,content)::l)
         )
       | SOME (id_non_termn (SOME x), m) => NONE
       | SOME (id_termn f, m) => SOME l
       )
   | NONE => NONE
  )
End





Definition determine_termn_new_def:
  determine_termn_new rec p =
  case rec.final(p) of
  | SOME b => id_termn (b)
  | _ => id_non_termn (NONE)
End



Definition determine_termn_list_new_def:
  determine_termn_list_new rec nodes_simp =
   MAP (\(n,x,p,p'). (n, x, (determine_termn_new rec p, p) , (determine_termn_new rec p',p') )) nodes_simp
End



Definition COUNT_LIST_local_def:
  (COUNT_LIST_local 0n = []) ∧
  (COUNT_LIST_local n = COUNT_LIST_local (n-1) ++ [n-1])
End



Definition mk_new_labels_content_new_def:
  mk_new_labels_content_new l =
    let
      all_contents = MAP (λ(n,x',((id,content),(id',content'))). content) l ++
                     MAP (λ(n,x',((id,content),(id',content'))). content') l;
      unique_contents = nub all_contents;
      indices = COUNT_LIST_local (LENGTH unique_contents)
    in
      ZIP (indices, unique_contents)
End


Definition mk_new_labels_id_new_def:
  mk_new_labels_id_new [] all_contents_inverse (c:num) =  [] ∧
  mk_new_labels_id_new ((n,x',((id,content),(id',content')))::rest) all_contents_inverse c =
   case (ALOOKUP all_contents_inverse content , ALOOKUP all_contents_inverse content' ) of
   | (SOME m , SOME q) => (c, (id,m))::(c+1, (id',q))::(mk_new_labels_id_new rest all_contents_inverse (c+2))
   | (_,_) => []
End





Definition non_term_leaf_updt_new_def:
  non_term_leaf_updt_new l1 x =
    MAP (λ(n, lbl).
      case lbl of
      | (id_termn f, m) => (n, (id_termn f, m))
      | (id_non_termn NONE, m) => (n, (id_non_termn (SOME x), m))
      | (id_non_termn (SOME x'), m) => (n, (id_non_termn (SOME x'), m))
        ) l1
End




Definition body_of_mk_new_def:
  body_of_mk_new rec (BDD:('a,'b) BDD_sep) (x:string) (c:num) =
  (let (r,edges,labels_id,labels_content) = BDD in
     (case getLeaves edges r of
      | SOME leaves =>
          (case (getLabels_new labels_id labels_content leaves) of
           | SOME leaves_labels =>
               ( let leaves_sub = leaves_pred_sub rec leaves_labels x in
                   let simp_leaves = simp_pred_list rec leaves_sub in
                     let simp_leaves' = determine_termn_list_new rec simp_leaves in

                       let new_labels_content = mk_new_labels_content_new simp_leaves' in
                         let new_labels_content_inverse = MAP (λ(a,b). (b,a)) new_labels_content in
                           let new_labels_id = mk_new_labels_id_new simp_leaves' new_labels_content_inverse c in
                             let new_edges = mk_new_edges simp_leaves' c in
                               let label_leaf_updated = non_term_leaf_updt_new labels_id x
                               in
                                 SOME (((r,  edges ++ new_edges,
                                         label_leaf_updated++new_labels_id,
                                         new_labels_content):(('a,'b)BDD_sep)),
                                       c + (LENGTH new_labels_id)
                                      )
               )
           | NONE => NONE
          )
      | NONE => NONE
     )
  )
End



Definition mk_BDDPred_new_def:
  (mk_BDDPred_new rec (BDD:('a, 'b) BDD_sep) l [] c = SOME BDD) ∧
  (mk_BDDPred_new rec (BDD:('a, 'b) BDD_sep) l (x::xs) c =
   case body_of_mk_new rec BDD (x:string) (c:num) of
     SOME (BDD',c') => mk_BDDPred_new rec BDD' (x::l) xs c'
   | NONE => NONE
  )
End



(**************************)
(**  optimization part  ****)



(******************************************************)
(*                    merge_new Def                       *)
(******************************************************)




Definition eq_vars_in_labels_new_def:
  eq_vars_in_labels_new (labels_id: 'b label_id) n n' =
    case (ALOOKUP labels_id n', ALOOKUP labels_id n) of
    | (SOME (id_termn (a), m), SOME (id_termn (a'), m')) => (a = a')
    | (SOME (id_non_termn (SOME x), m), SOME (id_non_termn (SOME x'), m')) => (x = x')
    | (SOME (id_non_termn (NONE), m), SOME (id_non_termn (NONE), m')) => (m=m')
    | _ => F
End




Definition mergable_new_def:
  mergable_new ((r,edges,labels_id):'b BDD_mini)  n n' =
  (n≠n' ∧ ALOOKUP edges n = ALOOKUP edges n' ∧
   eq_vars_in_labels_new labels_id n n' ∧ ALOOKUP labels_id n'  ≠ NONE )
End




Definition merge_new_def:
  merge_new ((r,edges,labels_id):'b BDD_mini) n n' =
  let edges' = merge_edges (edges:edges) n n' in
    let edges'' = ADELKEY n' edges' in
      let labels_id' = ADELKEY n' labels_id in
          (r,edges'',labels_id')
End



Definition eliminable_new_def:
  eliminable_new ((r,edges,labels_id):'b BDD_mini) n =
    case ALOOKUP edges n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           has_parent edges n1 n
        then SOME n1
        else NONE
    | NONE => NONE
End




Type distrub_st = ‘:( (string, (num list) option) alist   # num list # num list)’


Definition distrubute_labels_new_def:
  (distrubute_labels_new [] (acc:distrub_st) = acc) ∧
  (distrubute_labels_new ((n,lbl,m)::labels_id) (internals, ntl, tl) =
   case lbl of
   | id_termn _ => distrubute_labels_new labels_id (internals, ntl, n::tl)
   | id_non_termn (NONE) => distrubute_labels_new labels_id (internals, n::ntl, tl)
   | id_non_termn (SOME x)  => distrubute_labels_new labels_id (update_internals [] internals n x, ntl, tl)
  )
End



Definition bdd_distribute_new_def:
  bdd_distribute_new labels_id order =
    let internals_init = MAP (\x. (x,NONE)) order in
      distrubute_labels_new labels_id (internals_init, [],[])
End




Definition merge_new_safe_new_def:
  merge_new_safe_new (BDD_mini:'b BDD_mini) n n' =
  if mergable_new BDD_mini n n' then
    (T, merge_new BDD_mini n n')
   else
    (F, BDD_mini)
End



Definition eliminate_safe_new_def:
  eliminate_safe_new (BDD_mini:'b BDD_mini) n =
  case eliminable_new BDD_mini n  of
  | SOME n' =>  (T, merge_new BDD_mini n' n)
  | NONE => (F,BDD_mini)
End

Definition mergable_projection_new_def:
  mergable_projection_new edges_proj labels_id_proj n n' =
  (n≠n' ∧ ALOOKUP edges_proj n = ALOOKUP edges_proj n' ∧
   eq_vars_in_labels_new labels_id_proj n n' ∧ ALOOKUP labels_id_proj n'  ≠ NONE )
End

Definition optimize_node_new_def:
  (optimize_node_new edges_proj labels_id_proj (BDD_mini:'b BDD_mini) n [] = SND (eliminate_safe_new BDD_mini n)) ∧

  (optimize_node_new edges_proj labels_id_proj BDD_mini n (n'::nl) =
   case eliminable_projection edges_proj n of
   | SOME n' =>  SND (eliminate_safe_new BDD_mini n)
   | NONE => (
     case mergable_projection_new edges_proj labels_id_proj n' n of
     | T => ( case merge_new_safe_new BDD_mini n' n of
              | (T, BDD_mini') => BDD_mini'
              | (F, BDD_mini') => optimize_node_new edges_proj labels_id_proj BDD_mini n nl
            )

     | F => optimize_node_new edges_proj labels_id_proj BDD_mini n nl)
  )
End



Definition optimize_layer_new_def:
  (optimize_layer_new edges_proj labels_id_proj (BDD_mini:'b BDD_mini) [] = BDD_mini) ∧
  (optimize_layer_new edges_proj labels_id_proj BDD_mini  (n::nl)=
   optimize_layer_new edges_proj labels_id_proj (optimize_node_new edges_proj labels_id_proj BDD_mini n nl) nl
  )
End



Definition project_edges_to_new_def:
  project_edges_to_new edges nl =
    MAP (\n. (n,THE(ALOOKUP edges n))) nl
End

Definition project_labels_to_new_def:
  project_labels_to_new labels_id nl =
    MAP (\n. (n,THE(ALOOKUP labels_id n))) nl
End


Definition optimize_internals_new_def:
  (optimize_internals_new (BDD_mini:'b BDD_mini) [] = BDD_mini) ∧
  (optimize_internals_new BDD_mini  ((var,NONE)::l) = optimize_internals_new BDD_mini l) ∧

  (optimize_internals_new (r,edges,labels_id)  ((var,SOME nl)::l)=
    let edges_proj = project_edges_to_new edges nl in
     let labels_id_proj = project_labels_to_new labels_id nl in
      let BDD_mini' = optimize_layer_new edges_proj labels_id_proj (r,edges,labels_id)  nl in
         optimize_internals_new BDD_mini' l
  )
End


Definition optimize_bdd_new_def:
  optimize_bdd_new ((r,edges,labels_id):'b BDD_mini) order =
  let (internals,ntl,tl) = bdd_distribute_new labels_id order in
    let labels_id_proj_tl = project_labels_to_new labels_id tl in (* projection for terminals *)
      let labels_id_proj_ntl = project_labels_to_new labels_id ntl in (* projection for non-terminals *)
        let BDD_mini1 = optimize_layer_new [] labels_id_proj_tl (r,edges,labels_id) tl in
          let BDD_mini2 = optimize_layer_new [] labels_id_proj_ntl BDD_mini1 ntl in
            optimize_internals_new BDD_mini2 internals
End





Definition mk_BDDPred_opt_new_def:
  (mk_BDDPred_opt_new rec (BDD_sep:('b, 'a) BDD_sep) l [] c =
                           SOME (BDD_sep)
  ) ∧

  (mk_BDDPred_opt_new rec (BDD_sep) l (x::xs) c =

   case (body_of_mk_new rec BDD_sep (x:string) (c:num)) of
   | SOME ((r,edges,labels_id,labels_content) ,c') =>

       ( let (r',edges',labels_id') = optimize_bdd_new (r,edges,labels_id) (x::l) in
           mk_BDDPred_opt_new rec (r',edges',labels_id', labels_content) (x::l) xs c'
       )

   | NONE => NONE
  )
End

*)

val _ = export_theory ();
