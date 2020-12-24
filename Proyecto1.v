Require Import Lia.
Require Import BinNat.
Require Import BinNums.
Require Import BinNatDef.
Require Import BinPos.

Include BinNat.N.

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

Definition zeroBit (k m: N) : bool :=
N.eqb (N.land k m) 0.

(* Todo número binario es igual a sí mismo. *)
Lemma bin_eq: forall (b: N), N.eqb b b = true.
Proof.
intro.
apply eqb_eq.
trivial.
Qed.

Module BinTrie.

(* Para que no me diga que empty require un parámetro. *)
Set Asymmetric Patterns.

(* Empezamos por definir tries binarios como en el artículo. *)
Inductive binTrie: Type :=
| empty : binTrie
| leaf: nat -> binTrie
| trie: binTrie -> binTrie -> binTrie.

(* Función de búsqueda *)
Fixpoint lookup (key: N) (t: binTrie) : option nat :=
match t with
| empty => None
| leaf x => Some x
| trie t1 t2 => if (N.even key) then lookup (N.div2 key) t1
                else lookup (N.div2 key) t2
end.

(* Constructor inteligente *)
Definition smartTrie (t1 t2: binTrie) : binTrie :=
match t1, t2 with
| empty, empty => empty
| _, _ => trie t1 t2
end.

(* Teorema: Podemos construir con trie o con smartTrie sin afectar lookup *)
Theorem lookup_cons_indep: forall (t1 t2: binTrie) (k: N),
lookup k (trie t1 t2) = lookup k (smartTrie t1 t2).
Proof.
intros.
destruct t1, t2; simpl; trivial.
apply obvious_if.
Qed.

End BinTrie.

(* Optimización 1: Colapsar subárboles vacíos en una sola hoja *)
Module BinTrie2.

(* Trie binario en el que las hojas guardan parte de la llave *)
Inductive binTrie: Type :=
| empty : binTrie
| leaf: N -> nat -> binTrie
| trie: binTrie -> binTrie -> binTrie.

(* Nuevo constructor inteligente. *)
Definition smartTrie (t1 t2: binTrie): binTrie :=
match t1, t2 with
| empty, empty => empty
| leaf j x, empty => leaf (2*j) x
| empty, leaf j x => leaf (2*j+1) x
| _, _ => trie t1 t2
end.

(* Función de búsqueda *)
Fixpoint lookup (key: N) (t: binTrie) : option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j key) then Some x
              else None
| trie t1 t2 => if (N.even key) then lookup (N.div2 key) t1
                else lookup (N.div2 key) t2
end.

End BinTrie2.

Module BinTrie3.

(* Nueva optimización, cada nodo guarda el bit en el que se divide.
 * Es decir, si tenemos un nodo que se divide así:
 *                       n
 *                      / \
 *                     i   d
 * Entonces el nodo n guarda 2^x donde x es su profundidad.
 * i y d guardarían 2^(x+1) (si no son hojas)
 *)

(* Tipo de tries binarios *)
Inductive binTrie: Type :=
| empty : binTrie
| leaf: N -> nat -> binTrie
| trie: N -> binTrie -> binTrie -> binTrie.


(* Nueva función de búsqueda *)
Fixpoint lookup (key: N) (t: binTrie) : option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j key) then Some x
              else None
| trie m t1 t2 => if (zeroBit key m) then lookup key t1
                else lookup key t2
end.

(* Nuevo constructor inteligente. 
 * m es el bit en el que se divide el árbol 
 * Ya no hay que multiplicar para las hojas porque ahora guardan la 
 * dirección exacta. *)
Definition smartTrie (m: N) (t1 t2: binTrie): binTrie :=
match t1, t2 with
| empty, empty => empty
| leaf j x, empty => leaf j x
| empty, leaf j x => leaf j x
| _, _ => trie m t1 t2
end.

End BinTrie3.

Module PatriciaTrees.
(* Última optimización que vuelve a nuestros tries árboles Patricia. *)

(* Árboles Patricia *)
Inductive patriciaTree: Type :=
| empty : patriciaTree
| leaf: N -> nat -> patriciaTree
| trie: N -> N -> patriciaTree -> patriciaTree -> patriciaTree.

(* Función de máscara.
 * m es un entero de la forma 2^i *)
Definition mask (k m: N): N :=
N.land k (N.pred m).

(* Función que revisa si dos enteros tienen los primeros x bits iguales. 
 * m es 2^x *)
Definition matchPrefix (k p m: N) : bool :=
N.eqb (mask k m) p.

(* Nueva función de búsqueda 
 * Igual a la del caso pasado, solo que ahora los nodos guardan el prefijo
 * común de sus hijos. *)
Fixpoint lookup (k: N) (t: patriciaTree) : option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j k) then Some x
              else None
| trie p m t0 t1 => if (zeroBit k m) then lookup k t0
                    else lookup k t1
end.

(* Nuevo constructor inteligente. *)
Definition br (p m: N) (p1 p2: patriciaTree) : patriciaTree :=
match p1, p2 with
| empty, _ => p2
| _, empty => p1
| _, _ => trie p m p1 p2
end.

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
      rewrite zero.
      rewrite bin_eq.
      trivial.
    * simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
+ simpl.
  destruct (matchPrefix k n n0) eqn:prefix.
  - destruct (zeroBit k n0) eqn:zero.
    * simpl.
      rewrite zero.
      apply IHp1.
      simpl in H.
      rewrite zero in H.
      trivial.
    * simpl.
      rewrite zero.
      apply IHp2.
      simpl in H.
      rewrite zero in H.
      trivial.
  - unfold join.
    destruct (zeroBit k (branchingBit k n)) eqn:zero.
    * simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
    * simpl.
      rewrite zero.
      rewrite bin_eq.
      trivial.
Qed.
      
      
    


End PatriciaTrees.





