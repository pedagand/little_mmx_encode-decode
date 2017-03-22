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
  apply operand_to_bin_hypothesis1_t_n in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis2_t_n in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis3_t_n in H4.
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
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i (instr_opcode_t_i i))) f = f (tag_t_i (instr_opcode_t_i i))) by reflexivity.
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
  apply operand_to_bin_hypothesis1_t_i in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis2_t_i in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis3_t_i in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i := instr_opcode_t_i i;
       instr_operande1_t_i := instr_operande1_t_i i;
       instr_operande2_t_i := instr_operande2_t_i i;
       instr_operande3_t_i := instr_operande3_t_i i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  reflexivity.
Qed.



Lemma encode_decode_d_n : forall (i : instruction_duo_n) (bi : binary_instruction),
    encode_d_n i = Some bi -> decode bi = Some (instr_d_n i).
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
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_encdecP in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_n (instr_opcode_d_n i))) f = f (tag_d_n (instr_opcode_d_n i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis1_d_n in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis2_d_n in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_n := instr_opcode_d_n i;
       instr_operande1_d_n := instr_operande1_d_n i;
       instr_operande2_d_n := instr_operande2_d_n i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  reflexivity.
Qed.


Lemma encode_decode_d_i : forall (i : instruction_duo_i) (bi : binary_instruction),
    encode_d_i i = Some bi -> decode bi = Some (instr_d_i i).
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
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_encdecP in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_i (instr_opcode_d_i i))) f = f (tag_d_i (instr_opcode_d_i i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis1_d_i in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis2_d_i in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_i := instr_opcode_d_i i;
       instr_operande1_d_i := instr_operande1_d_i i;
       instr_operande2_d_i := instr_operande2_d_i i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  reflexivity.
Qed.



Lemma encode_decode : forall (i : instruction) (bi : binary_instruction),
    encode i = Some bi -> decode bi = Some i.
Proof.
  destruct i.
  -apply encode_decode_t_n.
  -apply encode_decode_t_i.
  -apply encode_decode_d_n.
  -apply encode_decode_d_i.
Qed.
  
