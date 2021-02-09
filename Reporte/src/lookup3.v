(* Nueva función de búsqueda *)
Fixpoint lookup3 (key: N) (t: binTrie3) : option nat :=
match t with
| empty3 => None
| leaf3 j x => if (N.eqb j key) then Some x
              else None
| trie3 m t1 t2 => if (zeroBit key m) then lookup3 key t1
                else lookup3 key t2
end.
