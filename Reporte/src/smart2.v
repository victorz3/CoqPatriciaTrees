(* Nuevo constructor inteligente. *)
Definition smartTrie2 (t1 t2: binTrie2): binTrie2 :=
match t1, t2 with
| empty2, empty2 => empty2
| leaf2 j x, empty2 => leaf2 (2*j) x
| empty2, leaf2 j x => leaf2 (2*j+1) x
| _, _ => trie2 t1 t2
end.
