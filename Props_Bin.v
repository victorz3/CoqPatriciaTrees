Require Import BinNat.
Require Import BinPos.
Include BinNat.N.

From Proyecto Require Export Defs_Bin.


(* Todo número binario es igual a sí mismo. *)
Lemma bin_eq: forall (b: N), N.eqb b b = true.
Proof.
intro.
apply eqb_eq.
trivial.
Qed.

(* Equivalencia entre mi podd y el odd de Coq. *)
Theorem podd_correct: forall (p: positive), N.odd (Npos p) = podd p.
Proof.
unfold N.odd.
induction p; reflexivity.
Qed.

(* Nuestra división entre 2 es equivalente a la de coq *)
Theorem pdiv2_correct: forall (p: positive), p <> xH -> 
Npos (pdiv2 p) = N.div2 (Npos p).
Proof.
induction p.
+ reflexivity.
+ reflexivity.
+ intro.
  contradiction.
Qed.

(* El XOR de un positivo con si mismo es 0. *)
Theorem pos_xor_zero: forall p, Pos.lxor p p = N0.
Proof.
induction p.
- simpl.
  rewrite IHp.
  reflexivity.
- simpl.
  rewrite IHp.
  reflexivity.
- reflexivity.
Qed.

(* XOR de un número con si mismo siempre es 0. *)
Theorem xor_zero: forall k, N.lxor k k = N0.
Proof.
destruct k.
+ reflexivity.
+ simpl.
  apply pos_xor_zero.
Qed.

(* Xor de dos positivos distintos no es 0. *)
Theorem xor_not_zero_pos: forall k1 k2, k1 <> k2 -> Pos.lxor k1 k2 <> N0.
Proof.
induction k1.
+ intros.
  simpl.
  destruct k2.
  - unfold Pos.Ndouble.
    assert (Pos.lxor k1 k2 <> 0%N).
    * apply IHk1.
      intro contra.
      rewrite contra in H.
      contradiction H.
      trivial.
    * destruct (Pos.lxor k1 k2) eqn:lxor.
      ++ assumption.
      ++ discriminate.
  - unfold Pos.Nsucc_double.
    destruct (Pos.lxor k1 k2).
    * discriminate.
    * discriminate.
  - discriminate. 
+ intros.
  destruct k2.
  - simpl.
    unfold Pos.Nsucc_double.
    destruct (Pos.lxor k1 k2); discriminate.
  - simpl.
    unfold Pos.Ndouble.
    destruct (Pos.lxor k1 k2) eqn:xor.
    * apply IHk1 in xor.
      ++ exfalso.
         assumption.
      ++ intro.
         rewrite H0 in H.
         contradiction H.
         trivial.
    * discriminate.
  - destruct k1.
    * simpl.
      discriminate.
    * simpl.
      discriminate.
    * simpl.
      discriminate.
+ intros.
  destruct k2; simpl.
  - discriminate.
  - discriminate.
  - contradiction H.
    reflexivity.
Qed.

(* Xor de dos números distintos no es 0. *)
Theorem xor_not_zero: forall k1 k2, k1 <> k2 -> N.lxor k1 k2 <> N0.
Proof.
induction k1.
+ simpl.
  intros.
  intuition.
+ intros.
  simpl.
  destruct k2.
  - assumption.
  - apply xor_not_zero_pos.
    intro.
    rewrite H0 in H.
    contradiction H.
    reflexivity.
Qed.

Lemma obvious_matchP: forall k x, matchPrefix k (mask k x) x = true.
Proof.
intros.
unfold matchPrefix.
rewrite bin_eq.
trivial.
Qed.

(* Un número siempre tiene branchingBit 0 con si mismo *)
Lemma zeroBit_self: forall k, zeroBit k (branchingBit k k) = true.
Proof.
intro.
unfold branchingBit.
unfold lowestBit.
unfold zeroBit.
destruct k.
+ reflexivity.
+ rewrite xor_zero.
  simpl.
  trivial.
Qed.

(* Lema auxiliar *)
Lemma branchingBit_zero_r: forall x, branchingBit x N0 = lowestBit x.
Proof.
intro.
unfold branchingBit.
destruct x eqn:X.
+ reflexivity.
+ reflexivity.
Qed.


(* La máscara de un número con su bit prendido más pequeño es 0. *)
Lemma mask_lowestBit: forall p, mask (pos p) (lowestBit (pos p)) = N0.
Proof.
destruct p.
+ reflexivity.
+ Admitted.

(* Lema auxiliar *)
Lemma compl_matchP: forall a x, matchPrefix a (mask x (branchingBit x a)) (branchingBit x a) = true.
Proof.
induction a.
+ simpl.
  intro.
  destruct x eqn:X.
  * reflexivity.
  * rewrite branchingBit_zero_r.
    simpl.
    destruct (Pos.pred_N (lowestBitP p)) eqn:Pos.
    - reflexivity.
    - unfold matchPrefix.
      unfold mask.
      simpl.
Admitted. 