Require Import BinNat.
Include BinNat.N.

(* Todo número binario es igual a sí mismo. *)
Lemma bin_eq: forall (b: N), N.eqb b b = true.
Proof.
intro.
apply eqb_eq.
trivial.
Qed.
