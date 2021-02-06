(* Definición de la función fst para naturales. *)
Definition fst (n1 n2: nat) : nat := n1.

(* Definición de una función que toma otra función y dos parámetros y devuelve
   la aplicación de la segunda función a los parámetros con órden invertido. *)
Definition swap (c: nat -> nat -> nat) (n1 n2: nat) : nat := c n2 n1.