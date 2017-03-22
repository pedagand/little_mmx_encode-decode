Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.


Lemma encode_decode_t_n : forall (i : instruction_tern_n) (bi : binary_instruction),
    encode_t_n i = Some bi -> decode bi = Some (instr_t_n i).
Proof.
  (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).  
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_encdecP in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_n (instr_opcode_t_n i))) f = f (tag_t_n (instr_opcode_t_n i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite. 
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis1 in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis2 in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis3 in H4.
  rewrite H4.  
  assert ({|
       instr_opcode_t_n := instr_opcode_t_n i;
       instr_operande1_t_n := instr_operande1_t_n i;
       instr_operande2_t_n := instr_operande2_t_n i;
       instr_operande3_t_n := instr_operande3_t_n i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  reflexivity.
Qed.
 
Lemma encode_decode_t_i : forall (i : instruction_tern_i) (bi : binary_instruction),
    encode_t_i i = Some bi -> decode bi = Some (instr_t_i i).
  Admitted.
