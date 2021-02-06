Require Import BinNat.

From Proyecto Require Export Defs_Bin.

(* Última optimización que vuelve a nuestros tries árboles Patricia. *)

(* Árboles Patricia *)
Inductive patriciaTree: Type :=
| empty : patriciaTree
| leaf: N -> nat -> patriciaTree
| trie: N -> N -> patriciaTree -> patriciaTree -> patriciaTree.

(* Nueva función de búsqueda 
 * Igual a la del caso pasado, solo que ahora los nodos guardan el prefijo
 * común de sus hijos. *)
Fixpoint lookup (k: N) (t: patriciaTree) : option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j k) then Some x
              else None
| trie p m t0 t1 => if (negb (matchPrefix k p m)) then None
                    else if (zeroBit k m) then lookup k t0
                         else lookup k t1
end.

(* Función de búsqueda equivalente a la primera pero un poco más eficiente. *)
Fixpoint lookup2 (k: N) (t:patriciaTree) :option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j k) then Some x
              else None
| trie p m t0 t1 => if (zeroBit k m) then lookup2 k t0
                         else lookup2 k t1
end. 

(* Nuevo constructor inteligente. *)
Definition br (p m: N) (p1 p2: patriciaTree) : patriciaTree :=
match p1, p2 with
| empty, _ => p2
| _, empty => p1
| _, _ => trie p m p1 p2
end.


