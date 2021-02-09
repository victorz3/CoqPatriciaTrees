(* Función de búsqueda equivalente a la primera pero un poco más eficiente. *)
Fixpoint lookup2 (k: N) (t:patriciaTree) :option nat :=
match t with
| empty => None
| leaf j x => if (N.eqb j k) then Some x
              else None
| trie p m t0 t1 => if (zeroBit k m) then lookup2 k t0
                         else lookup2 k t1
end. 
