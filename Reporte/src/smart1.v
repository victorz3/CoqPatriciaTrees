(* Constructor inteligente *)
Definition smartTrie1 (t1 t2: binTrie1) : binTrie1 :=
match t1, t2 with
| empty1, empty1 => empty1
| _, _ => trie1 t1 t2
end.
