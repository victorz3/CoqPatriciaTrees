Require Import BinNat.

From Proyecto Require Export Defs_Patricia.
From Proyecto Require Export Defs_Misc.
From Proyecto Require Export Props_Bin.

(* Después de insertar en un árbol, es no vacío. *)
Lemma insert_non_empty: forall c k x t, insert c k x t <> empty.
Proof.
intros.
destruct t.
+ simpl.
  discriminate.
+ simpl.
  destruct (N.eqb n k).
  - discriminate.
  - unfold join.
    * destruct (zeroBit k (branchingBit k n)).
      ++ discriminate.
      ++ discriminate.
+ simpl.
  - destruct (matchPrefix k n n0).
    * destruct (zeroBit k n0).
      ++ discriminate.
      ++ discriminate.
    * unfold join.
      destruct (zeroBit k (branchingBit k n)).
      ++ discriminate.
      ++ discriminate.
Qed.

(* Las hojas son correctas. *)
Lemma correct_leaf: forall j y, correct (leaf j y).
Proof.
intros.
assert(insert fst j y empty = leaf j y).
+ simpl.
  trivial.
+ rewrite <- H.
  constructor.
  constructor.
Qed.

(* Si en un árbol que no contiene a k, inserto (k, x), entonces buscar k me
 * da x *)
Theorem lookup_after_insert: forall (c: nat -> nat -> nat) (k: N) 
                                    (x: nat) (p: patriciaTree),
lookup k p = None -> lookup k (insert c k x p) = Some x.
Proof.
intros.
induction p.
+ simpl.
  assert ((k =? k)%N = true).
  - apply bin_eq.
  - rewrite H0.
    trivial.
+ simpl.
  destruct (N.eqb n k) eqn:equality.
  - simpl in H.
    rewrite equality in H.
    inversion H.
  - unfold join.
    destruct (zeroBit k (branchingBit k n)) eqn:zero.
    * simpl.
      rewrite obvious_matchP.
      simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
    * simpl.
      rewrite obvious_matchP.
      simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
+ simpl.
  destruct (matchPrefix k n n0) eqn:pre.
  - destruct (zeroBit k n0) eqn:zero.
    * simpl.
      rewrite pre.
      simpl.
      rewrite zero.
      apply IHp1.
      simpl in H.
      rewrite pre in H.
      simpl in H.
      rewrite zero in H.
      trivial.
    * simpl.
      rewrite pre.
      simpl.
      rewrite zero.
      apply IHp2.
      simpl in H.
      rewrite pre in H.
      simpl in H.
      rewrite zero in H.
      trivial.
  - unfold join.
    destruct (zeroBit k (branchingBit k n)) eqn:zero.
    * simpl.
      rewrite obvious_matchP.
      simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
    * simpl.
      rewrite obvious_matchP.
      simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
Qed.

(* Si en un árbol que contiene a k, inserto (k, x) bajo la función f, 
 * entonces buscar k me da f(lo que había en k, x) *)
Theorem lookup_after_insert_function: forall (c: nat -> nat -> nat) (k: N) 
                                      (x y: nat) (p: patriciaTree),
lookup k p = Some y -> lookup k (insert c k x p) = Some (c x y).
Proof.
intros.
induction p.
+ simpl in H.
  inversion H.
+ simpl.
  destruct (N.eqb n k) eqn:equal.
  * simpl.
    rewrite bin_eq.
    simpl in H.
    rewrite equal in H.
    inversion H.
    trivial.
  * unfold join.
    destruct (zeroBit k (branchingBit k n)) eqn:zero.
    - simpl in H.
      rewrite equal in H.
      inversion H.
    - simpl in H.
      rewrite equal in H.
      inversion H.
+ simpl in H.
  destruct (matchPrefix k n n0) eqn:prefix.
  * simpl.
    rewrite prefix.
    destruct (zeroBit k n0) eqn:zero.
    - simpl.
      rewrite prefix.
      simpl.
      rewrite zero.
      apply IHp1.
      simpl in H.
      trivial.
    - simpl.
      rewrite prefix.
      simpl.
      rewrite zero.
      apply IHp2.
      simpl in H.
      trivial.
  * simpl in H.
    inversion H.
Qed.