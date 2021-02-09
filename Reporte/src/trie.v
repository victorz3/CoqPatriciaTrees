(* Empezamos por definir tries binarios como en el artículo. *)
Inductive binTrie1: Type :=
| empty1 : binTrie1
| leaf1: nat -> binTrie1
| trie1: binTrie1 -> binTrie1 -> binTrie1.
