(* Trie binario en el que las hojas guardan parte de la llave *)
Inductive binTrie2: Type :=
| empty2: binTrie2
| leaf2: N -> nat -> binTrie2
| trie2: binTrie2 -> binTrie2 -> binTrie2.
