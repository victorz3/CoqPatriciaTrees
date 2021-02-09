(* Tipo de tries binarios *)
Inductive binTrie3: Type :=
| empty3 : binTrie3
| leaf3: N -> nat -> binTrie3
| trie3: N -> binTrie3 -> binTrie3 -> binTrie3.
