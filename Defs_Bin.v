Require Import BinNat.

(* Definiciones para números binarios. *)

(* Nos dice si el m-ésimo bit de k es 0. *)
Definition zeroBit (k m: N) : bool :=
N.eqb (N.land k m) 0.

(* Función de máscara.
 * m es un entero de la forma 2^i *)
Definition mask (k m: N): N :=
N.land k (N.pred m).

(* Función que revisa si dos enteros tienen los primeros x bits iguales. 
 * m es 2^x *)
Definition matchPrefix (k p m: N) : bool :=
N.eqb (mask k m) p.