(* Nos dice si el m-ésimo bit de k es 0. *)
Definition zeroBit (k m: N) : bool :=
N.eqb (N.land k m) 0.
