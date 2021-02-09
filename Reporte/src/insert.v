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
