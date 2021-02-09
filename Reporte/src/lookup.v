(* Función de búsqueda *)
Fixpoint lookup1 (key: N) (t: binTrie1) : option nat :=
match t with
| empty1 => None
| leaf1 x => Some x
| trie1 t1 t2 => if (N.even key) then lookup1 (N.div2 key) t1
                else lookup1 (N.div2 key) t2
end.
