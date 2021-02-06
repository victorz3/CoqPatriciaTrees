Require Import BinNat.
Require Import BinPos.

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

(* Función que decide si un número positivo es impar. *)
Definition podd (n: positive) : bool :=
match n with
| xH => true
| xO _ => false
| xI _ => true
end.

(* División entre 2 para números positivos. 
 * Esta operación funciona solo para números distintos de 1. *)
Definition pdiv2 (n: positive) : positive :=
match n with
| xH => xH 
| xO n' => n'
| xI n' => n'
end.

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
