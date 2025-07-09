fun pairBDDs (bdd1: term, bdd2: term) =
let
    open pairSyntax numSyntax listSyntax;
    
    (* Helper: Convert HOL num to Arbnum.num *)
    fun num_to_arbnum num_term = 
        if is_numeral num_term then
            dest_numeral num_term
        else raise Fail "Not a numeral";
    
    (* Helper: Convert edge list *)
    fun convert_edges edges_term =
        let
            val (list_items, _) = dest_list edges_term
            fun convert_item item_term =
                let
                    val (node, children) = dest_pair item_term
                    val (left, right) = dest_pair children
                in
                    (num_to_arbnum node, (num_to_arbnum left, num_to_arbnum right))
                end
        in
            map convert_item list_items
        end;
    
    (* Destructure BDD terms as nested pairs *)
    val (root1_t, rest1) = dest_pair bdd1
    val (edges1_t, labels1_t) = dest_pair rest1
    val (root2_t, rest2) = dest_pair bdd2
    val (edges2_t, labels2_t) = dest_pair rest2
    
    val root1 = num_to_arbnum root1_t
    val root2 = num_to_arbnum root2_t
    val edges1 = convert_edges edges1_t
    val edges2 = convert_edges edges2_t
    
    (* Lookup children in edge list *)
    fun lookupChildren node edges =
        case List.find (fn (n, _) => Arbnum.compare(n, node) = EQUAL) edges of
            SOME (_, (l, r)) => (SOME l, SOME r)
          | NONE => (NONE, NONE)
    
    val queue = ref [(root1, root2)]
    val visited = ref []
    
    fun processQueue () =
        case !queue of
            [] => rev (!visited)
          | (n1, n2)::rest =>
            let
                fun isVisited pair = List.exists (fn p => p = pair) (!visited)
                val _ = queue := rest
                val newPair = (n1, n2)
                val _ = visited := newPair :: (!visited)
                val (l1, r1) = lookupChildren n1 edges1
                val (l2, r2) = lookupChildren n2 edges2
                val newLeft = 
                    case (l1, l2) of
                        (SOME left1, SOME left2) => [(left1, left2)]
                      | _ => []
                val newRight = 
                    case (r1, r2) of
                        (SOME right1, SOME right2) => [(right1, right2)]
                      | _ => []
                val newPairs = newLeft @ newRight
                val notVisited = List.filter (fn pair => not (isVisited pair)) newPairs
            in
                queue := !queue @ notVisited;
                processQueue ()
            end
    
    (* Convert result to HOL term *)
    fun to_hol_pair (a, b) = 
        mk_pair(mk_numeral a, mk_numeral b)
    val arbnum_pairs = processQueue ()
in
    mk_list(map to_hol_pair arbnum_pairs, 
           mk_prod(num, num))
end