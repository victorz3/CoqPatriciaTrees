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

(* 0 es neutro en xor. *)
Theorem xor_neutral: forall x, N.lxor x N0 = x.
Proof.
destruct x.
+ reflexivity.
+ destruct p; reflexivity.
Qed.

(* Xor conmuta para positivos. *)
Theorem xor_comm_pos: forall p1 p2, Pos.lxor p1 p2 = Pos.lxor p2 p1.
induction p1.
+ intro.
  simpl.
  destruct p2 eqn:P2.
  - rewrite IHp1.
    reflexivity.
  - rewrite IHp1.
    reflexivity.
  - reflexivity.
+ intro.
  simpl.
  destruct p2 eqn:P2.
  - rewrite IHp1; reflexivity.
  - rewrite IHp1; reflexivity.
  - reflexivity.
+ intro.
  destruct p2 eqn:P2; reflexivity.
Qed.

(* lxor es conmutativo *)
Theorem xor_comm: forall n1 n2, N.lxor n1 n2 = N.lxor n2 n1.
Proof.
destruct n1, n2.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ simpl; rewrite xor_comm_pos; trivial.
Qed.

(* branchingBit es conmutativo. *)
Lemma branchingBit_comm: forall x k, branchingBit x k = branchingBit k x.
Proof.
intros.
unfold branchingBit.
rewrite xor_comm.
trivial.
Qed.

(* Predecesor de 1 es 0 *)
Lemma pred_1: forall x, Pos.pred_N x = N0 -> x = xH.
Proof.
destruct x; simpl.
+ intro.
  inversion H.
+ intro.
  inversion H.
+ intro.
  trivial.
Qed. 

(* El predecesor del doble del bit más bajo de un número es es el predecesor del
   número con un 1 pegado.*)
Lemma pred_double_pred: forall (x w:positive), Pos.pred_N (lowestBitP x) = pos w -> Pos.pred_double (lowestBitP x) = (xI w).
Proof.
induction x.
+ intros.
  simpl in H.
  inversion H.
+ intros.
  simpl in H.
  simpl.
  inversion H.
  trivial.
+ intros.
  simpl in H.
  inversion H.
Qed.

Lemma lowestBit_mask: forall x, mask x (lowestBit x) = N0.
Proof.
induction x.
+ reflexivity.
+ induction p.
  - reflexivity.
  - simpl.
    simpl in IHp.
    destruct (Pos.pred_N (lowestBitP p)) eqn:Predecessor.
    * unfold Pos.pred_N in Predecessor.
      ++ assert (lowestBitP p = 1%positive).
         -- destruct (lowestBitP p) eqn:Low.
            ** inversion Predecessor.
            ** inversion Predecessor.
            ** trivial.
         -- rewrite H.
            reflexivity. 
    * apply pred_double_pred in Predecessor.
      rewrite Predecessor.
      rewrite IHp.
      reflexivity.
  - reflexivity.
Qed.

(* Multiplicar por dos es pegar un 0 *)
Theorem Ndouble_0: forall p, Pos.Ndouble (pos p) = pos (p~0).
Proof.
destruct p; reflexivity.
Qed.

(* Lemma auxiliar sobre branchingBit. *)
Lemma branchingBit_end1: forall p1 p2 x, branchingBit (pos p1) (pos p2) = pos x -> 
                                         branchingBit (pos p1~1) (pos p2~1) = pos x~0.
Proof.
induction p1.
+ intros.
  unfold branchingBit.
  simpl.
  unfold branchingBit in H; simpl in H. 
  destruct p2 eqn:P2.
  - simpl.
    destruct (Pos.Ndouble (Pos.lxor p1 p)) eqn:Double.
    * simpl in H.
      inversion H.
    * rewrite Ndouble_0.
      simpl in H.
      simpl.
      inversion H.
      trivial.
  - unfold lowestBit in H.
    unfold Pos.Nsucc_double in H.
    destruct (Pos.lxor p1 p) eqn:Xor.
    * simpl in H.
      simpl.
      inversion H.
      trivial.
    * simpl in H.
      inversion H.
      reflexivity.
  - unfold lowestBit in H.
    simpl in H.
    unfold lowestBit.
    simpl.
    inversion H.
    trivial.
+ intros.
  unfold branchingBit in H.
  simpl in H.
  destruct p2 eqn:P2.
  - unfold lowestBit in H.
    destruct (Pos.lxor p1 p) eqn:Xor.
    * simpl in H.
      inversion H.
      unfold branchingBit.
      simpl.
      rewrite Xor.
      reflexivity.
    * unfold branchingBit.
      simpl.
      rewrite Xor.
      simpl.
      inversion H.
      trivial.
  - destruct (Pos.lxor p1 p) eqn:Xor.
    * inversion H.
    * inversion H.
      unfold branchingBit.
      simpl.
      rewrite Xor.
      reflexivity.
  - inversion H.
    unfold branchingBit.
    reflexivity.
+ intros.
  unfold branchingBit in H.
  inversion H.
  destruct p2 eqn:P2.
  - unfold branchingBit.
    simpl.
    inversion H1.
    trivial.
  - inversion H1.
    unfold branchingBit; reflexivity.
  - inversion H1.
Qed.
    
(* Auxiliar, predecesor del doble es predecesor del número con un 0 pegado *)
Lemma pred_double_pred_0: forall x, pos (Pos.pred_double x) = N.pred (pos (x~0)).
Proof.
destruct x; reflexivity.
Qed.

(* Auxiliar *)
Lemma first_branchingBit: forall p1 p2, branchingBit (pos p1~0) (pos p2~1) = (pos xH).
Proof.
unfold branchingBit.
unfold lowestBit.
intros.
destruct (N.lxor (pos p1~0) (pos p2~1)) eqn:Xor.
+ simpl in Xor.
  unfold Pos.Nsucc_double in Xor.
  - destruct (Pos.lxor p1 p2) eqn:Xor2.
    * inversion Xor.
    * inversion Xor.
+ destruct p eqn:P.
  - reflexivity.
  - simpl in Xor.
    unfold Pos.Nsucc_double in Xor.
    destruct (Pos.lxor p1 p2) eqn:Xor2.
    * inversion Xor.
    * inversion Xor.
  - reflexivity.
Qed. 

(* Lema auxiliar para positivos *)
Lemma obvious_matchP_pos: forall p x, matchPrefix (pos p) (mask x (branchingBit x (pos p)))
  (branchingBit x (pos p)) = true.
Proof.
induction p.
+ intro.
  unfold matchPrefix.
  simpl.
  destruct x eqn:X.
  - reflexivity.
  - simpl.
    destruct p0 eqn:P0.
    * simpl.
      destruct (branchingBit (pos p1) (pos p)) eqn:Branch.
      ++ unfold branchingBit in Branch.
         simpl in Branch.
         destruct (Pos.lxor p1 p) eqn:Xor.
         -- unfold branchingBit.
            simpl.
            rewrite Xor.
            reflexivity.
         -- destruct p2 eqn:P2.
            ** simpl in Branch.
               inversion Branch.
            ** inversion Branch.
            ** inversion Branch.
      ++ rewrite (branchingBit_end1 p1 p p2).
         -- simpl.
            destruct p2 eqn:P2.
            ** unfold branchingBit in Branch.
               simpl in Branch.
               destruct (Pos.lxor p1 p) eqn:Xor.
               +++ inversion Branch.
               +++ destruct p4 eqn:P4; inversion Branch.
            ** simpl.
               unfold matchPrefix in IHp.
               unfold branchingBit in IHp.
               unfold branchingBit in Branch.
               unfold lowestBit in Branch.
               destruct (N.lxor (pos p1) (pos p)) eqn:Xor.
               +++ inversion Branch.
               +++ simpl in IHp.
                   assert (Hip:= (IHp (pos p1))).
                   rewrite Xor in Hip.
                   destruct (lowestBit (pos p4)) eqn:Low.
                   --- unfold lowestBit in Low.
                       inversion Low.
                   --- destruct p5 eqn:P5.
                       *** simpl in Hip.
                           simpl in Low.
                           inversion Low.
                           inversion Branch.
                           rewrite H0 in H1.
                           inversion H1.
                       *** simpl in Hip.
                           inversion Low; inversion Branch.
                           rewrite H0 in H1.
                           inversion H1.
                           rewrite <- H2.
                           apply eqb_eq in Hip.
                           rewrite Hip.
                           apply eqb_eq.
                           trivial.
                       *** simpl in Low; inversion Branch; inversion Low.
                           rewrite H0 in H1; inversion H1.
            ** reflexivity.
         -- trivial.
    * simpl.
      rewrite first_branchingBit.
      reflexivity.
    * simpl.
Admitted.
      
Lemma obvious_matchP2: forall k x, matchPrefix k (mask x (branchingBit x k))
             (branchingBit x k) = true.
Proof.
induction k.
+ unfold matchPrefix.
  intro.
  simpl.
  rewrite branchingBit_comm.
  unfold branchingBit.
  simpl.
  rewrite lowestBit_mask.
  trivial.
+ intro.
  unfold matchPrefix.
  simpl.
  destruct (N.pred (branchingBit x (pos p))) eqn:Pred.
  - simpl.
Admitted. 

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

(* El bit más pequeño prendido de un número que termina en 0 no es el último. *)
Lemma lowestBit_not_last: forall p, lowestBitP (xO p) = xO (lowestBitP p).
Proof.
destruct p; reflexivity.
Qed.

(* Si el doble de un número es 0, el número es 0. *)
Lemma double_zero: forall p, Pos.Ndouble p = N0 -> p = N0.
induction p.
+ reflexivity.
+ intros.
  simpl in H.
  inversion H.
Qed.

(* La máscara conserva bit 0. *)
Lemma mask_cons_0: forall p q, mask (pos (xO p)) (pos (xO q)) = N0 -> mask (pos p) (pos q) = N0.
Proof.
induction p.
+ intros.
  destruct q eqn:Q.
  - simpl.
    simpl in H.
    apply double_zero in H.
    trivial.
  - simpl in H.
    simpl.
    apply double_zero in H; trivial.
  - reflexivity.
+ intros.
  simpl.
  destruct (Pos.pred_N q) eqn:Predq.
  - trivial.
  - destruct p0 eqn:P0.
    * simpl in IHp.
Admitted.

(* La máscara de un número con su bit prendido más pequeño es 0. *)
Lemma mask_lowestBit: forall p, mask (pos p) (lowestBit (pos p)) = N0.
Proof.
destruct p.
+ reflexivity.
+ induction p.
  - reflexivity.
  - unfold lowestBit.
    rewrite lowestBit_not_last.
Admitted.

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