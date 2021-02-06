Require Import BinNat.

From Proyecto Require Export Defs_Bin.

(* Para que no me diga que empty require un parámetro. *)
Set Asymmetric Patterns.

(* Empezamos por definir tries binarios como en el artículo. *)
Inductive binTrie1: Type :=
| empty1 : binTrie1
| leaf1: nat -> binTrie1
| trie1: binTrie1 -> binTrie1 -> binTrie1.

(* Función de búsqueda *)
Fixpoint lookup1 (key: N) (t: binTrie1) : option nat :=
match t with
| empty1 => None
| leaf1 x => Some x
| trie1 t1 t2 => if (N.even key) then lookup1 (N.div2 key) t1
                else lookup1 (N.div2 key) t2
end.

(* Constructor inteligente *)
Definition smartTrie1 (t1 t2: binTrie1) : binTrie1 :=
match t1, t2 with
| empty1, empty1 => empty1
| _, _ => trie1 t1 t2
end.

(* Optimización 1: Colapsar subárboles vacíos en una sola hoja *)

(* Trie binario en el que las hojas guardan parte de la llave *)
Inductive binTrie2: Type :=
| empty2: binTrie2
| leaf2: N -> nat -> binTrie2
| trie2: binTrie2 -> binTrie2 -> binTrie2.

(* Nuevo constructor inteligente. *)
Definition smartTrie2 (t1 t2: binTrie2): binTrie2 :=
match t1, t2 with
| empty2, empty2 => empty2
| leaf2 j x, empty2 => leaf2 (2*j) x
| empty2, leaf2 j x => leaf2 (2*j+1) x
| _, _ => trie2 t1 t2
end.

(* Función de búsqueda *)
Fixpoint lookup2 (key: N) (t: binTrie2) : option nat :=
match t with
| empty2 => None
| leaf2 j x => if (N.eqb j key) then Some x
              else None
| trie2 t1 t2 => if (N.even key) then lookup2 (N.div2 key) t1
                else lookup2 (N.div2 key) t2
end.

(* Nueva optimización, cada nodo guarda el bit en el que se divide.
 * Es decir, si tenemos un nodo que se divide así:
 *                       n
 *                      / \
 *                     i   d
 * Entonces el nodo n guarda 2^x donde x es su profundidad.
 * i y d guardarían 2^(x+1) (si no son hojas)
 *)

(* Tipo de tries binarios *)
Inductive binTrie3: Type :=
| empty3 : binTrie3
| leaf3: N -> nat -> binTrie3
| trie3: N -> binTrie3 -> binTrie3 -> binTrie3.


(* Nueva función de búsqueda *)
Fixpoint lookup3 (key: N) (t: binTrie3) : option nat :=
match t with
| empty3 => None
| leaf3 j x => if (N.eqb j key) then Some x
              else None
| trie3 m t1 t2 => if (zeroBit key m) then lookup3 key t1
                else lookup3 key t2
end.

(* Nuevo constructor inteligente. 
 * m es el bit en el que se divide el árbol 
 * Ya no hay que multiplicar para las hojas porque ahora guardan la 
 * dirección exacta. *)
Definition smartTrie3 (m: N) (t1 t2: binTrie3): binTrie3 :=
match t1, t2 with
| empty3, empty3 => empty3
| leaf3 j x, empty3 => leaf3 j x
| empty3, leaf3 j x => leaf3 j x
| _, _ => trie3 m t1 t2
end.


