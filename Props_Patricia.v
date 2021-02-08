Require Import BinNat.
Require Import Bool.Bool.
Require Import Lia.

From Proyecto Require Export Defs_Patricia.
From Proyecto Require Export Defs_Misc.
From Proyecto Require Export Props_Bin.
From Proyecto Require Export Props_Misc.

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

(* Después de insertar, el tamaño se incrementa en 1. *)
Theorem insert_size: forall t c x y, lookup x t = None -> sizeP (insert c x y t) = S (sizeP t).
Proof.
induction t.
+ intros.
  reflexivity.
+ intros.
  simpl.
  destruct (N.eqb n x) eqn:Equal.
  - simpl in H.
    rewrite Equal in H.
    inversion H.
  - unfold join.
    * destruct (zeroBit x (branchingBit x n)) eqn:Zero.
      ++ reflexivity.
      ++ reflexivity.
+ intros.
  simpl.
  destruct (matchPrefix x n n0) eqn:Prefix.
  - simpl in H.
    rewrite Prefix in H.
    simpl in H.
    destruct (zeroBit x n0) eqn:Zero.
    * simpl.
      rewrite IHt1.
      ++ reflexivity.
      ++ trivial.
    * simpl.
      rewrite IHt2.
      ++ lia.
      ++ trivial.
  - unfold join.
    destruct (zeroBit x (branchingBit x n)) eqn:Zero.
    * simpl.
      trivial.
    * simpl.
      lia.
Qed.

(* Correcto de un árbol implica hijos correctos. *)
Theorem correct_children: forall t, correct t -> correct (left t) /\ correct (right t).
Proof.
intros.
induction H.
+ split; constructor.
+ split.
  - destruct t eqn:T.
    * simpl.
      constructor.
    * simpl.
      destruct (N.eqb n k) eqn:Equal.
      ++ simpl; constructor.
      ++ unfold join.
         destruct (zeroBit k (branchingBit k n)) eqn:Zero.
         -- simpl.
            apply correct_leaf.
         -- simpl.
            apply correct_leaf.
    * simpl.
      destruct (matchPrefix k n n0) eqn:Prefix.
      ++ destruct (zeroBit k n0) eqn:Zero.
         -- simpl.
            destruct IHcorrect.
            simpl in H0.
            constructor.
            trivial.
         -- simpl.
            destruct IHcorrect.
            simpl in H0.
            trivial.
      ++ unfold join.
         destruct (zeroBit k (branchingBit k n)) eqn:Zero.
         -- simpl.
            apply correct_leaf.
         -- simpl.
            trivial.
  - destruct t eqn:T.
    * simpl.
      constructor.
    * simpl.
      destruct (N.eqb n k) eqn:Equal.
      ++ simpl; constructor.
      ++ unfold join.
         destruct (zeroBit k (branchingBit k n)) eqn:Zero.
         -- simpl.
            apply correct_leaf.
         -- simpl.
            apply correct_leaf.
    * simpl.
      destruct (matchPrefix k n n0) eqn:Prefix.
      ++ destruct (zeroBit k n0) eqn:Zero.
         -- simpl.
            destruct IHcorrect.
            simpl in H1.
            trivial.
         -- simpl.
            destruct IHcorrect.
            simpl in H1.
            constructor;trivial.
      ++ unfold join.
         destruct (zeroBit k (branchingBit k n)) eqn:Zero.
         -- simpl.
            trivial.
         -- simpl.
            apply correct_leaf.
Qed.

(* Si en un árbol que no contiene a k, inserto (k, x), entonces buscar k me
 * da x *)
Theorem lookup2_after_insert_none: forall (c: nat -> nat -> nat) (k k0: N) 
                                    (x: nat) (p: patriciaTree),
lookup2 k p = None -> k <> k0 -> lookup2 k (insert c k0 x p) = None.
Proof. 
Admitted.


(* lookup después de insert y lookup2 después de insert dan lo mismo en 
   árboles correctos *)
Lemma lookup_insert_eq: forall p k c x y, lookup k p = lookup2 k p -> lookup k (insert c x y p) = lookup2 k (insert c x y p).
Proof.
induction p.
+ intros.
  reflexivity.
+ intros.
  simpl.
  destruct (N.eqb n x) eqn:Equal.
  - reflexivity.
  - unfold join.
    * destruct (zeroBit x (branchingBit x n)) eqn:Zero.
      ++ simpl.
         destruct (matchPrefix k (mask x (branchingBit x n)) (branchingBit x n)) eqn:Prefix.
         -- reflexivity.
         -- simpl.
            destruct (zeroBit k (branchingBit x n)) eqn:Zero2.
            ** destruct (N.eqb x k) eqn:Equal2.
               +++ apply eqb_eq in Equal2.
                   rewrite Equal2 in Prefix; rewrite obvious_matchP in Prefix; inversion Prefix.
               +++ trivial.
            ** destruct (N.eqb n k) eqn:Equal2.
               +++ apply eqb_eq in Equal2; rewrite Equal2 in Prefix; rewrite obvious_matchP2 in Prefix; inversion Prefix.
               +++ trivial.
      ++ simpl.
         destruct (matchPrefix k (mask x (branchingBit x n)) (branchingBit x n)) eqn:Prefix.
         -- reflexivity.
         -- simpl; destruct (zeroBit k (branchingBit x n)) eqn:Zero2.
            ** destruct (N.eqb n k) eqn:Equal2; trivial.
               apply eqb_eq in Equal2; rewrite Equal2 in Prefix; rewrite obvious_matchP2 in Prefix; inversion Prefix.
            ** destruct (N.eqb x k) eqn:Equal2; trivial.
               apply eqb_eq in Equal2; rewrite Equal2 in Prefix; rewrite obvious_matchP in Prefix; inversion Prefix.
+ intros.
  simpl.
  destruct (matchPrefix x n n0) eqn:Prefix; trivial.
  - destruct (zeroBit x n0) eqn:Zero; trivial.
    * simpl.
      destruct (matchPrefix k n n0) eqn:Prefix2; simpl; trivial.
      ++ destruct (zeroBit k n0) eqn:Zero2.
         -- simpl in H.
            rewrite Prefix2 in H; simpl in H.
            rewrite Zero2 in H; simpl in H.
            apply IHp1; trivial.
         -- simpl in H.
            rewrite Prefix2 in H; simpl in H.
            rewrite Zero2 in H; simpl in H.
            trivial.
      ++ destruct (zeroBit k n0) eqn:Zero2.
         -- simpl in H.
            rewrite Prefix2 in H; simpl in H.
            rewrite Zero2 in H; simpl in H.
            destruct (eq_dec k x).
            ** rewrite e in Prefix2; rewrite Prefix2 in Prefix; inversion Prefix.
            ** assert (lookup2 k (insert c x y p1) = None). 
               +++ apply lookup2_after_insert_none.
                   --- intuition.
                   --- trivial.
               +++ intuition.
         -- simpl in H.
            rewrite Prefix2 in H; simpl in H.
            rewrite Zero2 in H; simpl in H.
            trivial.
    * simpl.
      destruct (matchPrefix k n n0) eqn:Prefix2.
      ++ simpl.
         destruct (zeroBit k n0) eqn:Zero2.
         -- simpl in H.
            rewrite Zero2 in H; simpl in H.
            rewrite Prefix2 in H; simpl in H.
            trivial.
         -- apply IHp2.
            simpl in H.
            rewrite Zero2 in H; simpl in H.
            rewrite Prefix2 in H; simpl in H.
            trivial.
      ++ simpl.
         destruct (zeroBit k n0) eqn:Zero2.
         -- simpl in H.
            rewrite Zero2 in H; simpl in H.
            rewrite Prefix2 in H; simpl in H.
            trivial.
         -- assert (lookup2 k (insert c x y p2) = None).
            ** apply lookup2_after_insert_none.
               +++ simpl in H.
                   rewrite Zero2 in H; simpl in H.
                   rewrite Prefix2 in H; simpl in H.
                   rewrite H; trivial.
               +++ intro.
                   rewrite H0 in Prefix2; rewrite Prefix in Prefix2; inversion Prefix2.
            ** rewrite H0; trivial.
  - unfold join.
    destruct (zeroBit x (branchingBit x n)) eqn:Zero.
    * simpl.
      ++ destruct (matchPrefix k (mask x (branchingBit x n)) (branchingBit x n)) eqn:Prefix2.
         -- simpl.
            destruct (zeroBit k (branchingBit x n)) eqn:Zero2; trivial.
         -- simpl.
            destruct (zeroBit k (branchingBit x n)) eqn:Zero2.
            ** destruct (N.eqb x k) eqn:Equal; trivial.
               apply eqb_eq in Equal; rewrite Equal in Prefix2; rewrite obvious_matchP in Prefix2; inversion Prefix2.
            ** destruct (zeroBit k n0) eqn:Zero3.
               +++ simpl in H.
                   destruct (eq_dec k x).
                   --- rewrite <- e in Zero; rewrite <- e in Zero2; rewrite Zero in Zero2; inversion Zero2.
                   --- destruct (matchPrefix k n n0) eqn:Prefix3.
                       *** simpl in H.
                           (* Contradicción n0 > branchingBit x n > n0 *)
                           admit.
                       *** simpl in H.
                           rewrite Zero3 in H.
                           trivial.
               +++ simpl in H.
                   destruct (matchPrefix k n n0) eqn:Prefix3.
                   --- simpl in H.
                       (* Contradicción n0 > branchingBit x n > n0 *)
                       admit.
                   --- simpl in H.
                       rewrite Zero3 in H.
                       trivial.
    * simpl.
      destruct (matchPrefix k (mask x (branchingBit x n)) (branchingBit x n)) eqn:Prefix2.
      ++ simpl.
         destruct (zeroBit k (branchingBit x n)) eqn:Zero2.
         -- destruct (matchPrefix k n n0) eqn:Prefix3.
            ** simpl.
               simpl in H.
               rewrite Prefix3 in H.
               simpl in H.
               trivial.
            ** simpl.
               simpl in H.
               rewrite Prefix3 in H.
               simpl in H.
               trivial.
         -- trivial.
      ++ simpl.
         simpl in H.
         destruct (matchPrefix k n n0) eqn:Prefix3.
         -- simpl in H.
            destruct (zeroBit k (branchingBit x n)) eqn:Zero2.
            ** admit. (*Misma contradicción de antes *)
            ** destruct (N.eqb x k) eqn: Equal;trivial.
               apply eqb_eq in Equal; rewrite Equal in Prefix2; rewrite obvious_matchP in Prefix2; inversion Prefix2.
         -- simpl in H.
            destruct (zeroBit k (branchingBit x n)) eqn:Zero2; trivial.
            destruct (N.eqb x k) eqn:Equal; trivial.
            apply eqb_eq in Equal; rewrite Equal in Prefix2; rewrite obvious_matchP in Prefix2; inversion Prefix2.
Admitted.
                  
                        
                    
            
      
    


(* lookup y lookup2 son equivalentes en un árbol correcto. *)
Theorem lookup_eq: forall t k, correct t -> lookup k t = lookup2 k t.
Proof.
intros.
destruct H.
+ reflexivity.
+ apply lookup_insert_eq.
  trivial.
Qed.