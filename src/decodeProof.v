Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.


Lemma decode_encode : forall (bi : binary_instruction) (i : instruction),
    length bi = 32 -> decode bi = Some i -> encode i = Some bi.
Proof.
  intros.  
  unfold decode in H0.
  destruct (get_first_n_bit bi 8).
  Search bind.
  apply bind_rewrite in H0.
  destruct H0.
  destruct (get_first_n_bit l0 8).
  destruct x.
  -destruct (get_first_n_bit l2 8).
   destruct (get_first_n_bit l4 8).
   rewrite  ret_rewrite in H0.
   destruct H0.
   unfold encode.
   
   
  