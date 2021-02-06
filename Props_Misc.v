Require Import Lia.

(* Un if con ambas ramas iguales es igual al resultado de las ramas. *)
Lemma obvious_if: forall (A: Type) (b:bool) (x: A), (if b then x else x) = x.
Proof.
intros.
destruct b; reflexivity.
Qed.

(* 2n es par para toda n... *)
Lemma even_2n: forall (n:nat), Nat.even(2*n) = true.
Proof.
induction n.
+ simpl; trivial.
+ simpl.
  assert (n + S (n + 0) = S (2 * n)).
  * lia.
  * rewrite H.
    trivial.
Qed.
