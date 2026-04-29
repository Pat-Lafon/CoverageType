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

  Axiom tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l.
  Axiom tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1.
  Axiom tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1.
  Axiom tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x.
  Axiom tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n.
  Axiom tree_depth_unique : forall (l : tree Z), forall (n : Z), forall (m : Z), (depth l n /\ depth l m) -> n = m.
  Axiom tree_depth_node : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ rch l l2))) -> ((n1 > n2 -> depth l (n1 + 1)) /\ (n2 >= n1 -> depth l (n2 + 1))).
  Axiom tree_lower_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (lower_bound l x /\ (lch l l1 /\ ~leaf l1)) -> lower_bound l1 x.
  Axiom tree_lower_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (rch l l1 /\ ~leaf l1))) -> lower_bound l1 x.
  Axiom tree_upper_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (upper_bound l x /\ (rch l l1 /\ ~leaf l1)) -> upper_bound l1 x.
  Axiom tree_upper_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (lch l l1 /\ ~leaf l1))) -> upper_bound l1 x.
  Axiom tree_depth_geq_0 : forall (l : tree Z) (n : Z), (depth l n) -> (n >= 0).
  Axiom tree_depth_0_is_leaf : forall (l : tree Z) (n : Z), (depth l n /\ n = 0) -> (leaf l).
  Axiom tree_lower_bound_root : forall (l : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ lower_bound l y) -> (y < x).
  Axiom tree_upper_bound_root : forall (l : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ upper_bound l y) -> (y > x).
  Axiom tree_bst_lch_bst : forall (l : tree Z) (l1 : tree Z), (lch l l1 /\ bst l) -> (bst l1).
  Axiom tree_bst_rch_bst : forall (l : tree Z) (l1 : tree Z), (rch l l1 /\ bst l) -> (bst l1).
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

  Lemma tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l. Admitted.
  Lemma tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1. Admitted.
  Lemma tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1. Admitted.
  Lemma tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x. Admitted.
  Lemma tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n. Admitted.
  Lemma tree_depth_unique : forall (l : tree Z), forall (n : Z), forall (m : Z), (depth l n /\ depth l m) -> n = m. Admitted.
  Lemma tree_depth_node : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ rch l l2))) -> ((n1 > n2 -> depth l (n1 + 1)) /\ (n2 >= n1 -> depth l (n2 + 1))). Admitted.
  Lemma tree_lower_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (lower_bound l x /\ (lch l l1 /\ ~leaf l1)) -> lower_bound l1 x. Admitted.
  Lemma tree_lower_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (rch l l1 /\ ~leaf l1))) -> lower_bound l1 x. Admitted.
  Lemma tree_upper_bound_destruct : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (upper_bound l x /\ (rch l l1 /\ ~leaf l1)) -> upper_bound l1 x. Admitted.
  Lemma tree_upper_bound_destruct_2 : forall (l : tree Z), forall (l1 : tree Z), forall (x : Z), (bst l /\ (root l x /\ (lch l l1 /\ ~leaf l1))) -> upper_bound l1 x. Admitted.
  Lemma tree_depth_geq_0 : forall (l : tree Z) (n : Z), (depth l n) -> (n >= 0).
  Proof.
    induction l; intros n Hd.
    - inversion Hd. lia.
    - simpl in Hd. destruct Hd as [nl [nr [Hd1 [Hd2 Hc]]]].
      apply IHl1 in Hd1.
      apply IHl2 in Hd2.
      intuition.
  Qed.

  Lemma tree_depth_0_is_leaf : forall (l : tree Z) (n : Z), (depth l n /\ n = 0) -> (leaf l).
  Proof.
    induction l; intros n [Hd Hn].
    - reflexivity.
    - subst. simpl in Hd.
      destruct Hd as [nl [nr [Hd1 [Hd2 Hc]]]].
      apply tree_depth_geq_0 in Hd1.
      apply tree_depth_geq_0 in Hd2.
      lia.
  Qed.

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

  Lemma tree_bst_lch_bst : forall (l : tree Z) (l1 : tree Z), (lch l l1 /\ bst l) -> (bst l1).
  Proof.
    intros [] l [Hl Hb]; try contradiction.
    simpl in *. subst.
    destruct Hb. assumption.
  Qed.

  Lemma tree_bst_rch_bst : forall (l : tree Z) (l1 : tree Z), (rch l l1 /\ bst l) -> (bst l1).
  Proof.
    intros [] r [Hr Hb]; try contradiction.
    simpl in *. subst.
    decompose [and] Hb. assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (d : Z), 0 <= d -> (forall (lo : Z), forall (hi : Z), lo < hi -> (forall (v : tree Z), (d > 0 /\ (~leaf v -> lower_bound v lo) /\ (~leaf v -> upper_bound v hi) /\ bst v /\ (exists (n3 : Z), depth v n3 /\ n3 <= d)) -> ((~d = 0 <-> d > 0) /\ ~d = 0 /\ (((lo + 1) < hi /\ (1 + lo) < hi /\ (exists (x : Z), lo < x /\ x < hi /\ ((0 <= (d - 1) /\ (d - 1) >= 0 /\ (d - 1) < d /\ lo < x /\ (exists (lt : tree Z), (~leaf lt -> lower_bound lt lo) /\ (~leaf lt -> upper_bound lt x) /\ bst lt /\ (exists (n1 : Z), depth lt n1 /\ n1 <= (d - 1)) /\ 0 <= (d - 1) /\ (d - 1) >= 0 /\ (d - 1) < d /\ x < hi /\ (exists (rt : tree Z), (~leaf rt -> lower_bound rt x) /\ (~leaf rt -> upper_bound rt hi) /\ bst rt /\ (exists (n2 : Z), depth rt n2 /\ n2 <= (d - 1)) /\ root v x /\ lch v lt /\ rch v rt /\ (exists (nl : Z), exists (nr : Z), depth lt nl /\ depth rt nr /\ (nl > nr -> depth v (nl + 1)) /\ (nr >= nl -> depth v (nr + 1)))))) \/ (leaf v /\ depth v 0)))) \/ (~(lo + 1) < hi /\ leaf v /\ depth v 0))))).
  Proof.
    intros d Hd lo hi Hlh v [Hd1 [Hlb [Hub [Hb [n [Hdn Hn]]]]]].
    repeat split; try lia.
    destruct (n =? 0) eqn:Hne.
    - assert (n = 0) by lia. destruct (lo + 1 <? hi) eqn:Hsep.
      * left. intuition.
        exists (lo + 1). intuition.
        right. intuition.
        + apply (tree_depth_0_is_leaf v n). intuition.
        + subst. assumption.
      * right. intuition.
        + apply (tree_depth_0_is_leaf v n). intuition.
        + subst. assumption. 
    - left.
      remember (tree_depth_geq_0 _ _ Hdn).
      assert (n > 0) by lia.
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
      exists x. intuition.
      left. intuition.
      exists l. intuition.
      * apply (tree_lower_bound_destruct v l). intuition.
      * apply (tree_upper_bound_destruct_2 v l). intuition.
      * apply (tree_bst_lch_bst v). intuition.
      * exists nl. intuition.
        destruct (nl >? nr) eqn:Hge.
        + assert (nl > nr) by lia. intuition.
          replace n with (nl + 1) in Hn by (apply (tree_depth_unique v); intuition).
          lia.
        + assert (nr >= nl) by lia. intuition.
          replace n with (nr + 1) in Hn by (apply (tree_depth_unique v); intuition).
          lia.
      * exists r. intuition.
        + apply (tree_lower_bound_destruct_2 v r). intuition.
        + apply (tree_upper_bound_destruct v r). intuition.
        + apply (tree_bst_rch_bst v). intuition.
        + exists nr. intuition.
          destruct (nl >? nr) eqn:Hge.
          -- assert (nl > nr) by lia. intuition.
             replace n with (nl + 1) in Hn by (apply (tree_depth_unique v); intuition).
             lia.
          -- assert (nr >= nl) by lia. intuition.
             replace n with (nr + 1) in Hn by (apply (tree_depth_unique v); intuition).
             lia.
        + exists nl. exists nr. intuition.
  Qed.
End Goal.
