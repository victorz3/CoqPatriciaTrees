(* Función de combinación.
   Usamos la medida de número de nodos para decirle a Coq que los 
   argumentos sí se decrementan 
 * Parámetros:
 * c - función a aplicar en caso de que la llave ya tenga elemento.
 * s t - árboles *)
Program Fixpoint merge (c : nat -> nat -> nat) (s t: patriciaTree) 
  {measure ((nodes s) + (nodes t))} : patriciaTree :=
match s, t with
| empty, _ => t
| _, empty => s
| leaf k x, _ => insert c k x t
| _, leaf k x => insert (swap c) k x t
| trie p m s0 s1, trie q n t0 t1 => if (N.eqb m n) && (N.eqb p q)
                                    (* Los árboles comparten prefijo *)
                                    then trie p m (merge c s0 t0) (merge c s1 t1)
                                    else if (N.ltb m n) && (matchPrefix q p m)
                                    (* Caso en que q contiene a p *)
                                         then if (zeroBit q m)
                                              then br p m (merge c s0 t) s1
                                              else br p m s0 (merge c s1 t)
                                         else if (N.ltb n m) && (matchPrefix p q n)
                                              then if (zeroBit p n)
                                                   then br q n (merge c s t0) t1
                                                   else br q n t0 (merge c s t1)
                                              else join p q s t
end.
