(* Árboles Patricia *)
Inductive patriciaTree: Type :=
| empty : patriciaTree
| leaf: N -> nat -> patriciaTree
| trie: N -> N -> patriciaTree -> patriciaTree -> patriciaTree.
