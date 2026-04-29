let[@axiom] tree_positive_depth_is_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0) #==> (not (leaf l))
let[@axiom] tree_no_leaf_exists_lch = fun (l : (int tree)) -> fun ((l1 [@ex]) : (int tree)) -> ((not (leaf l)) #==> (lch l l1))
let[@axiom] tree_no_leaf_exists_rch = fun (l : (int tree)) -> fun ((l1 [@ex]) : (int tree)) -> ((not (leaf l)) #==> (rch l l1))
let[@axiom] tree_no_leaf_exists_root = fun (l : (int tree)) -> fun ((x [@ex]) : int) -> ((not (leaf l)) #==> (root l x))
let[@axiom] tree_depth_exists (l : int tree) ((n [@exists]) : int) = depth l n
let[@axiom] tree_depth_unique (l : int tree) (n : int) (m : int) =
  (depth l n && depth l m)#==>(n == m)

let[@axiom] tree_depth_node (l : int tree) (l1 : int tree) (l2 : int tree) (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2) #==> (((n1 > n2) #==> (depth l (n1 + 1)))
  && ((n2 >= n1) #==> (depth l (n2 + 1))))

let[@axiom] tree_lower_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (lower_bound l x && lch l l1 && not (leaf l1))#==>(lower_bound l1 x)

let[@axiom] tree_lower_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && rch l l1 && not (leaf l1))#==>(lower_bound l1 x)

let[@axiom] tree_upper_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (upper_bound l x && rch l l1 && not (leaf l1))#==>(upper_bound l1 x)

let[@axiom] tree_upper_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && lch l l1 && not (leaf l1))#==>(upper_bound l1 x)
