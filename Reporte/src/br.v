(* Nuevo constructor inteligente. *)
Definition br (p m: N) (p1 p2: patriciaTree) : patriciaTree :=
match p1, p2 with
| empty, _ => p2
| _, empty => p1
| _, _ => trie p m p1 p2
end.
