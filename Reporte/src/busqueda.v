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
