From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
  Parameter tree : forall (a : Type), Type.
  Parameter rbtree : forall (a : Type), Type.

  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.
  Parameter leaf : forall {a : Type}, tree a -> Prop.
  Parameter root : forall {a : Type}, tree a -> a -> Prop.
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter lower_bound : tree Z -> Z -> Prop.
  Parameter upper_bound : tree Z -> Z -> Prop.
  Parameter bst : tree Z -> Prop.
  Parameter bool_gen : unit -> Prop.
  Parameter int_range : Z -> Z -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.
  Parameter incr : Z -> Z.

  Axiom tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l.
  Axiom tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1.
  Axiom tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1.
  Axiom tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x.
  Axiom tree_depth_geq_0 : forall (l : tree Z), forall (n : Z), depth l n -> n >= 0.
  Axiom tree_depth_0_is_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n = 0) -> leaf l.
  Axiom tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n.
  Axiom tree_depth_unique : forall (l : tree Z), forall (n : Z), forall (m : Z), (depth l n /\ depth l m) -> n = m.
  Axiom tree_depth_node : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ rch l l2))) -> ((n1 > n2 -> depth l (n1 + 1)) /\ (n2 >= n1 -> depth l (n2 + 1))).
  Axiom tree_lower_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (lower_bound l x /\ (lch l l1 /\ ~leaf l1)) -> lower_bound l1 x.
  Axiom tree_lower_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (rch l l1 /\ ~leaf l1))) -> lower_bound l1 x.
  Axiom tree_upper_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (upper_bound l x /\ (rch l l1 /\ ~leaf l1)) -> upper_bound l1 x.
  Axiom tree_upper_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (lch l l1 /\ ~leaf l1))) -> upper_bound l1 x.
  Axiom tree_bst_lch_bst : forall (l : tree Z), forall (l1 : tree Z), (lch l l1 /\ bst l) -> bst l1.
  Axiom tree_bst_rch_bst : forall (l : tree Z), forall (l1 : tree Z), (rch l l1 /\ bst l) -> bst l1.
  Axiom tree_lower_bound_root : forall (l : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ lower_bound l y) -> (y < x).
  Axiom tree_upper_bound_root : forall (l : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ upper_bound l y) -> (y > x).
End Signatures.

Module Axioms : Signatures.
  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.
  Inductive rbtree' (a : Type) : Type :=
  | Rbtleaf : rbtree' a
  | Rbtnode : bool -> rbtree' a -> a -> rbtree' a -> rbtree' a.
  Definition rbtree := rbtree'.

  Fixpoint depth {a : Type} (t : tree a) (n : Z) : Prop :=
    match t with
    | Leaf _ => n = 0
    | Node _ _ l r => exists nl nr : Z, 
      depth l nl /\ depth r nr /\ n = Z.max nl nr + 1
    end.
  Definition leaf {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ _ _ => False
    end.
  Definition root {a : Type} (t : tree a) (x : a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ x' _ _ => x = x'
    end.
  Definition lch {a : Type} (t : tree a) (l : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ l1 _ => l1 = l
    end.
  Definition rch {a : Type} (t : tree a) (r : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ _ r1 => r1 = r
    end.
  Fixpoint lower_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => x < y /\ lower_bound l x /\ lower_bound r x
    end.
  Fixpoint upper_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => y < x /\ upper_bound l x /\ upper_bound r x
    end.
  Fixpoint bst (t : tree Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ x l r => bst l /\ bst r /\ upper_bound l x /\ lower_bound r x
    end.
  Parameter bool_gen : unit -> Prop.
  Parameter int_range : Z -> Z -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.
  Parameter incr : Z -> Z.

  Lemma tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l. Admitted.
  Lemma tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1. Admitted.
  Lemma tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1. Admitted.
  Lemma tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x. Admitted.
  Lemma tree_depth_geq_0 : forall (l : tree Z), forall (n : Z), depth l n -> n >= 0. Admitted.
  Lemma tree_depth_0_is_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n = 0) -> leaf l. Admitted.
  Lemma tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n. Admitted.
  Lemma tree_depth_unique : forall (l : tree Z), forall (n : Z), forall (m : Z), (depth l n /\ depth l m) -> n = m. Admitted.
  Lemma tree_depth_node : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ rch l l2))) -> ((n1 > n2 -> depth l (n1 + 1)) /\ (n2 >= n1 -> depth l (n2 + 1))). Admitted.
  Lemma tree_lower_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (lower_bound l x /\ (lch l l1 /\ ~leaf l1)) -> lower_bound l1 x. Admitted.
  Lemma tree_lower_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (rch l l1 /\ ~leaf l1))) -> lower_bound l1 x. Admitted.
  Lemma tree_upper_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (upper_bound l x /\ (rch l l1 /\ ~leaf l1)) -> upper_bound l1 x. Admitted.
  Lemma tree_upper_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (lch l l1 /\ ~leaf l1))) -> upper_bound l1 x. Admitted.
  Lemma tree_bst_lch_bst : forall (l : tree Z), forall (l1 : tree Z), (lch l l1 /\ bst l) -> bst l1. Admitted.
  Lemma tree_bst_rch_bst : forall (l : tree Z), forall (l1 : tree Z), (rch l l1 /\ bst l) -> bst l1. Admitted.
  Lemma tree_lower_bound_root : forall (l : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ lower_bound l y) -> (y < x).
  Proof.
    intros [] x y [Hb [Hr Hlb]]; try contradiction.
    simpl in *. subst.
    destruct Hlb. assumption.
  Qed.

  Lemma tree_upper_bound_root : forall (l : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ upper_bound l y) -> (y > x).
  Proof.
    intros [] x y [Hb [Hr Hub]]; try contradiction.
    simpl in *. subst.
    destruct Hub. lia.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (d : Z), 0 <= d -> (forall (lo : Z), forall (hi : Z), lo < hi -> (forall (v : tree Z), ((~leaf v -> lower_bound v lo) /\ (~leaf v -> upper_bound v hi) /\ bst v /\ (exists (n : Z), depth v n /\ n <= d)) -> ((~d = 0 <-> d > 0) /\ ((d = 0 /\ leaf v) \/ (~d = 0 /\ (((lo + 1) < hi /\ (exists (x : Z), (1 + lo) < hi /\ lo < x /\ x < hi /\ ((exists (lt_0 : tree Z), lo < x /\ (d - 1) < d /\ 0 <= (d - 1) /\ (~leaf lt_0 -> lower_bound lt_0 lo) /\ (~leaf lt_0 -> upper_bound lt_0 x) /\ bst lt_0 /\ (exists (n_7 : Z), depth lt_0 n_7 /\ n_7 <= (d - 1)) /\ (exists (rt_0 : tree Z), x < hi /\ (d - 1) < d /\ 0 <= (d - 1) /\ (~leaf rt_0 -> lower_bound rt_0 x) /\ (~leaf rt_0 -> upper_bound rt_0 hi) /\ bst rt_0 /\ (exists (n_8 : Z), depth rt_0 n_8 /\ n_8 <= (d - 1)) /\ root v x /\ lch v lt_0 /\ rch v rt_0)) \/ leaf v))) \/ (~(lo + 1) < hi /\ leaf v))))))).
  Proof.
    intros d Hd lo hi Hlh v [Hlb [Hub [Hbst [n [Hdpt Hn]]]]].
    intuition.
    destruct (d =? 0) eqn:Hdeq.
    - left. assert (d = 0) by lia. intuition.
      assert (n = 0) by (apply tree_depth_geq_0 in Hdpt; lia).
      apply (tree_depth_0_is_leaf v n). intuition.
    - right. assert (d > 0) by lia. intuition.
      destruct (n =? 0) eqn:Hneq.
      + assert (n = 0) by lia. intuition.
        assert (leaf v) by (apply (tree_depth_0_is_leaf v n); intuition).
        destruct (lo + 1 <? hi) eqn:Hlhc.
        * left. intuition.
          exists (lo + 1). intuition.
        * right. intuition.
      + left. assert (n > 0) by (apply tree_depth_geq_0 in Hdpt; lia).
        assert (~leaf v) by (apply (tree_positive_depth_is_not_leaf v n); intuition).
        destruct (tree_no_leaf_exists_root v) as [x Hrt].
        destruct (tree_no_leaf_exists_lch v) as [l Hl].
        destruct (tree_no_leaf_exists_rch v) as [r Hr].
        destruct (tree_depth_exists l) as [nl Hnl].
        destruct (tree_depth_exists r) as [nr Hnr].
        destruct (tree_depth_node v l r nl nr). { intuition. }
        assert (hi > x) by (apply (tree_upper_bound_root v); intuition).
        assert (lo < x) by (apply (tree_lower_bound_root v); intuition).
        intuition.
        exists x. intuition. left.
        exists l. intuition.
        * apply (tree_lower_bound_destruct v l). intuition.
        * apply (tree_upper_bound_destruct_2 v l). intuition.
        * apply (tree_bst_lch_bst v l). intuition.
        * exists nl. intuition.
          destruct (nl >? nr) eqn:Hge.
          -- assert (nl > nr) by lia. intuition.
             replace n with (nl + 1) in Hn by (apply (tree_depth_unique v); intuition).
             lia.
          -- assert (nr >= nl) by lia. intuition.
             replace n with (nr + 1) in Hn by (apply (tree_depth_unique v); intuition).
             lia.
        * exists r. intuition.
          -- apply (tree_lower_bound_destruct_2 v r). intuition.
          -- apply (tree_upper_bound_destruct v r). intuition.
          -- apply (tree_bst_rch_bst v r). intuition.
          -- exists nr. intuition.
             destruct (nl >? nr) eqn:Hge.
             ++ assert (nl > nr) by lia. intuition.
                replace n with (nl + 1) in Hn by (apply (tree_depth_unique v); intuition).
                lia.
             ++ assert (nr >= nl) by lia. intuition.
                replace n with (nr + 1) in Hn by (apply (tree_depth_unique v); intuition).
                lia.
  Qed.
End Goal.
