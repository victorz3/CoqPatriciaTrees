Require Import BinNat.

From Proyecto Require Export Defs_Trie.
From Proyecto Require Export Props_Misc.

(* Teorema: Podemos construir con trie1 o con smartTrie1 sin afectar lookup1 *)
Theorem lookup_cons_indep1: forall (t1 t2: binTrie1) (k: N),
lookup1 k (trie1 t1 t2) = lookup1 k (smartTrie1 t1 t2).
Proof.
intros.
destruct t1, t2; simpl; trivial.
apply obvious_if.
Qed.

(* Mismos teoremas para trie2 y trie3 *)

Theorem lookup_cons_indep2: forall (t1 t2: binTrie2) (k: N),
lookup2 k (trie2 t1 t2) = lookup2 k (smartTrie2 t1 t2).
Proof.
intros.
destruct t1 eqn:T1; destruct t2 eqn:T2; simpl; trivial.
+ apply obvious_if.
+ Admitted.



