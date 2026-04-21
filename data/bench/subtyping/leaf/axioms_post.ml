let[@axiom] tree_complete_leaf = fun (l : (int tree)) -> ((leaf l) #==> (complete l))
let[@axiom] tree_leaf_depth_0_alt = fun (l : (int tree)) -> ((leaf l) #==> (depth l 0))