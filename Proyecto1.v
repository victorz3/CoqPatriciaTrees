

Require Import BinNums.
Require Import BinNatDef.
Require Import BinPos.
From Proyecto Require Export Defs_Patricia.

Include BinNat.N.





Module BinTrie3.



End BinTrie3.

Module PatriciaTrees.

(* Función que decide si un número positivo es impar. *)
Definition podd (n: positive) : bool :=
match n with
| xH => true
| xO _ => false
| xI _ => true
end.

(* Equivalencia entre mi podd y el odd de Coq. *)
Theorem podd_correct: forall (p: positive), N.odd (Npos p) = podd p.
Proof.
unfold N.odd.
induction p; reflexivity.
Qed.

(* División entre 2 para números positivos. 
 * Esta operación funciona solo para números distintos de 1. *)
Definition pdiv2 (n: positive) : positive :=
match n with
| xH => xH 
| xO n' => n'
| xI n' => n'
end.

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

(* Función auxiliar que calcula el bit menos significativo de un número
 * positivo. *)
Fixpoint lowestBitP (x: positive): positive :=
match x with
| xO x' => Pos.mul 2 (lowestBitP x')
| _ => xH
end.

(* Función que obtiene el primer bit encendido de un número.
 * Esta función se puede calcular más rápidamente usando complemento a 2.
 * Pero como solo queremos verificar, no lo haremos de la manera más 
 * eficiente. *)
Definition lowestBit (x: N) : N :=
match x with
| N0 => N0
| Npos p => Npos (lowestBitP p)
end.

(* Función que obtiene el primer bit en que dos números difieren *)
Definition branchingBit (p0 p1: N) : N := lowestBit (N.lxor p0 p1).

(* Función que une dos árboles con prefijos incompatibles *)
Definition join (p0 p1: N) (t0 t1: patriciaTree) : patriciaTree :=
let m := branchingBit p0 p1 in
if zeroBit p0 m then trie (mask p0 m) m t0 t1
else trie (mask p0 m) m t1 t0.

(* Función de inserción 
 * Parámetros:
 * c - función a aplicar en caso de que la llave ya tenga elemento.
 * k - llave 
 * x - número a insertar
 * t - árbol *)
Fixpoint insert (c : nat -> nat -> nat) (k: N) (x: nat) (t: patriciaTree) :=
match t with
| empty => leaf k x
| leaf j y => if (N.eqb j k) then leaf k (c x y)
              else join k j (leaf k x) t
| trie p m t0 t1 => if (matchPrefix k p m) then 
                       if (zeroBit k m) then trie p m (insert c k x t0) t1
                       else trie p m t0 (insert c k x t1)
                    else join k p (leaf k x) t
end.


(* Después de insertar en un árbol, es no vacío. *)
Lemma insert_non_empty: forall c k x t, insert c k x t <> empty.
Proof.
intros.
destruct t0.
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


(* Un árbol es correcto si y solo si es el vacío o se construyó por medio
   de inserts. *)
Inductive correct: patriciaTree -> Prop :=
| corrempty : correct empty
| corrins: forall c k x t, correct t -> correct (insert c k x t).

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


(* Lema auxiliar *)
Lemma compl_matchP: forall a x, matchPrefix a (mask x (branchingBit x a)) (branchingBit x a) = true.
Proof.
intros.
unfold branchingBit.
destruct (eq_dec a x).
+ rewrite e.
  apply obvious_matchP.
+ unfold matchPrefix.
  unfold mask.
  unfold lowestBit.
  destruct (N.lxor x a) eqn:xor.
  - assert (N.lxor x a <> N0).
    * apply xor_not_zero.
      intuition.
    * intuition.
  - destruct p eqn:P.
    * simpl.
      destruct a, x; trivial.
    * simpl.
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

(* lookup y lookup2 son equivalentes en un árbol correcto. *)
Theorem lookup_eq: forall k t, correct t -> lookup k t = lookup2 k t.
Proof.
intros.
induction H.
+ reflexivity.
+ destruct t0.
  - reflexivity.
  - simpl.
    destruct (N.eqb n k0) eqn:igualdad.
    * reflexivity.
    * unfold join.
      destruct (zeroBit k0 (branchingBit k0 n)) eqn:zero.
      ++ simpl.
         destruct (matchPrefix k (mask k0 (branchingBit k0 n)) (branchingBit k0 n)) eqn:pre.
         -- reflexivity.
         -- simpl.
            destruct (zeroBit k (branchingBit k0 n)) eqn:zero2.
            ** destruct (N.eqb k0 k) eqn:iguald.
               +++ assert (k0 = k).
                   --- apply eqb_eq.
                       assumption.
                   --- rewrite H0 in pre.
                       assert (matchPrefix k (mask k (branchingBit k n)) (branchingBit k n) = true).
                       *** apply obvious_matchP.
                       *** rewrite pre in H1.
                           inversion H1.
               +++ reflexivity.
            ** destruct (N.eqb n k) eqn:nigualk.
               +++ apply eqb_eq in nigualk.
                   rewrite nigualk in pre.
                   rewrite compl_matchP in pre.
                   inversion pre.
               +++ trivial.
      ++ Admitted.
 
(* Si un árbol compuesto por dos subárboles es correcto, 
   entonces los dos subárboles también lo son. *)
Theorem correct_children: forall p m t0 t1, correct (trie p m t0 t1) ->
  correct t0 /\ correct t1.
Proof.
intros.
induction t0.
+ split.
  - constructor.
  - destruct t1.
    * constructor.
    * apply correct_leaf.
    * inversion H.
      inversion H0. 
Admitted.

(* Propiedad auxiliar que relaciona lookup y matchPrefix *)
Lemma lookup_impl_matchp: forall (t1 t2: patriciaTree) (k n n0: N), 
correct(trie n n0 t1 t2) -> (exists (x: nat), 
lookup k (trie n n0 t1 t2) = Some x) -> matchPrefix k n n0 = true.
Proof.
intros.
induction t1.
+ destruct t2.
  - simpl in H0.
    rewrite obvious_if in H0. 
    inversion H0.
    inversion H1.
Admitted.

Lemma obvious_matchP: forall k x, matchPrefix k (mask k x) x = true.
Proof.
intros.
unfold matchPrefix.
rewrite bin_eq.
trivial.
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


End PatriciaTrees.





