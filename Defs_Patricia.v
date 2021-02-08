Require Import BinNat.
Require Import Bool.Bool.
Require Import Lia.
Require Import Program.Wf.
Require Import Program.

From Proyecto Require Export Defs_Bin.
From Proyecto Require Export Defs_Misc.

(* Última optimización que vuelve a nuestros tries árboles Patricia. *)

(* Árboles Patricia *)
Inductive patriciaTree: Type :=
| empty : patriciaTree
| leaf: N -> nat -> patriciaTree
| trie: N -> N -> patriciaTree -> patriciaTree -> patriciaTree.

(* Tamaño de un Árbol Patricia *)
Fixpoint sizeP (p: patriciaTree) : nat :=
match p with
|empty => O
|leaf _ _ => S O
|trie x y t1 t2 => (sizeP t1) + (sizeP t2)
end.

(* Número de nodos en el árbol Patricia *)
Fixpoint nodes (p:patriciaTree) : nat :=
match p with
|empty => O
| leaf _ _ => S O
| trie x y t1 t2 => S ((nodes t1) + (nodes t2))
end.

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

(* Un árbol es correcto si y solo si es el vacío o se construyó por medio
   de inserts. *)
Inductive correct: patriciaTree -> Prop :=
| corrempty : correct empty
| corrins: forall c k x t, correct t -> correct (insert c k x t).

(* Subárbol izquierdo *)
Definition left (t: patriciaTree) : patriciaTree :=
match t with
|empty => empty
|leaf _ _ => empty
|trie _ _ t1 _ => t1
end.

(* Subárbol derecho *)
Definition right (t: patriciaTree) : patriciaTree :=
match t with
|empty => empty
|leaf _ _ => empty
|trie _ _ _ t2 => t2
end.

(* Función de combinación.
   Usamos la medida de número de nodos para decirle a Coq que los argumentos sí se decrementan 
 * Parámetros:
 * c - función a aplicar en caso de que la llave ya tenga elemento.
 * k - llave 
 * x - número a insertar
 * t - árbol *)
Program Fixpoint merge (c : nat -> nat -> nat) (s t: patriciaTree) {measure ((nodes s) + (nodes t))} : patriciaTree :=
match s, t with
| empty, _ => t
| _, empty => s
| leaf k x, _ => insert c k x t
| _, leaf k x => insert (swap c) k x t
| trie p m s0 s1, trie q n t0 t1 => if (N.eqb m n) && (N.eqb p q)
                                    (* Los árboles comparten prefijo *)
                                    then trie p m (merge c s0 t0) (merge c s1 t1)
                                    else if (N.ltb m n) && (matchPrefix q p m)
                                    (* Caso en que q contiene a p *)
                                         then if (zeroBit q m)
                                              then br p m (merge c s0 t) s1
                                              else br p m s0 (merge c s1 t)
                                         else if (N.ltb n m) && (matchPrefix p q n)
                                              then if (zeroBit p n)
                                                   then br q n (merge c s t0) t1
                                                   else br q n t0 (merge c s t1)
                                              else join p q s t
end.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
split.
- intros.
  intro.
  destruct H3.
  inversion H3.
- intros.
  intro.
  destruct H3.
  inversion H3.
Defined.