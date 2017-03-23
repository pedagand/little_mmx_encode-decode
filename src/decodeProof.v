Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.

Lemma get_first_n_bit_size_out : forall (n : nat) (bi l l0 : list bool),
    n <= length bi -> get_first_n_bit bi n = (l, l0) -> length l = n /\ length l0 = (length bi) - n.
Proof.
Admitted.

Lemma get_first_n_bit_with_size : forall (bi li tl: list bool) , length bi = 32 -> get_first_n_bit bi 8 = (li,tl) -> length li = 8 /\ length tl = 24.
Proof.
  intros.
  Search get_first_n_bit.
Admitted.

Lemma get_first_n_bit_res' : forall (n : nat) (l l1 l2 : list bool), length l = n -> get_first_n_bit l n = (l1, l2) -> l = l1 ++ [].
  induction n.
  -intros.
   Search get_first_n_bit.
   apply get_first_n_bit_size_out in H0.
   +destruct H0.
    Search (length _ = 0).
    apply length_zero_iff_nil in H0.
    apply length_zero_iff_nil in H.
    rewrite H0.
    rewrite H.
    reflexivity.
   +apply Peano.le_0_n.
  -intros.
   apply get_first_n_bit_size_out in H0.
   +destruct H0.
Admitted.
  
Lemma get_first_n_bit_res_16 : forall (l l1 l2 : list bool), get_first_n_bit l 16 = (l1, l2) -> l = l1 ++ l2.
  Admitted.

Lemma get_first_n_bit_res_8 : forall (l l1 l2 : list bool), get_first_n_bit l 8 = (l1, l2) -> l = l1 ++ l2.
Proof.
  destruct l.
  -intros.
   simpl in H.
   inversion H.
   reflexivity.
  -intros.
  
Admitted.
  






    
  

Lemma decode_encode : forall (bi : binary_instruction) (i : instruction),
    length bi = 32 -> decode bi = Some i -> encode i = Some bi.
Proof.
  intros.  
  unfold decode in H0.
  (* c'est quoi la façon de détruire (let (li, next) := get_first_n_bit bi 8 in mais en laissant en hypothèse (li, next) = get_first_n_bit bi 8 in *)
  destruct (get_first_n_bit bi 8) eqn:Hl1.
  Search bind.
  apply bind_rewrite in H0.
  destruct H0.
  destruct H0.
  destruct (get_first_n_bit l0 8) eqn:Hl2.
  destruct x.
  
  (* case instruction t_n *)
  -destruct (get_first_n_bit l2 8) eqn:Hl3.
   destruct (get_first_n_bit l4 8) eqn:Hl4.
   rewrite  ret_rewrite in H0.
   unfold encode.
   (* inversion H0. *)
   unfold encode_t_n.
   apply commut_equal in H1.
   apply lookdown_encdec in H1.
   inversion H0.
   inversion H0.
   assert (instr_opcode_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = t) by reflexivity.
   rewrite H2.
   rewrite H1.
   assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
   rewrite H5.
   (* these are premliminare assertion to refactor a little bit the code *)
   assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l0 = 24).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H8.
      simpl in H8.
      auto.
     -auto.
   }
   assert (8 <= length l0) by (rewrite H7; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l2 = 16).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H10.
      simpl in H10.
      apply get_first_n_bit_size_out in Hl2.
      +destruct Hl2.
       rewrite H12.
       rewrite H7.
       reflexivity.
      +auto.
     -auto.
   }
   assert (8 <= length l2) by (rewrite H9; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l4 = 8).
   {
     apply get_first_n_bit_size_out in Hl3.
     destruct Hl3.
     rewrite H12.
     rewrite H9.
     reflexivity.
     exact H10.
   }
   assert (8 <= length l4) by (rewrite H11; repeat apply le_n_S; apply Peano.le_0_n).
   assert (n_bit 8 (bit_n l) = Some l).
   {
     Check get_first_n_bit_size_out.
     apply get_first_n_bit_size_out in Hl1.
     apply bit_n_bit.
     -destruct Hl1.
     auto.
     -rewrite H.
      repeat apply le_n_S.
      Search (0 <= _).
      apply Peano.le_0_n.
   }
   rewrite H13.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
   rewrite H14.
   assert (instr_operande1_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
   rewrite H15.
   Search operand_to_bin.
   assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
   {
     unfold operand_to_bin.
     apply bit_n_bit.     
     apply get_first_n_bit_size_out in Hl2.
     -destruct Hl2.
      auto.
     -auto.
   }   
   rewrite H16.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
   rewrite H17.
   assert (instr_operande2_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
   rewrite H18.
   assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl3.
     -destruct Hl3.
      auto.
     -auto.
   }   
   rewrite H19.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
   rewrite H20.
   assert (instr_operande3_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l5)) by reflexivity.
   rewrite H21.
   assert (operand_to_bin (reg_o (reg (bit_n l5))) = Some l5).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl4.
     destruct Hl4.
     auto.
     auto.
   }   
   rewrite H22.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
   rewrite H23.
   assert (bi = (l ++ l1 ++ l3 ++ l5 ++ l6)). 
   {
     apply get_first_n_bit_res_8 in Hl1.
     apply get_first_n_bit_res_8 in Hl2.
     apply get_first_n_bit_res_8 in Hl3.
     apply get_first_n_bit_res_8 in Hl4.
     rewrite Hl1.
     rewrite Hl2.
     rewrite Hl3.
     rewrite Hl4.
     reflexivity.
   }
   assert (length l6 = 0).
   {
     apply get_first_n_bit_size_out in Hl4.
     -destruct Hl4.
      rewrite H26. rewrite H11. reflexivity.
     -auto.           
   }
   rewrite H24.
   apply length_zero_iff_nil in H25.
   rewrite H25.
   rewrite ret_rewrite.
   rewrite app_nil_r.
   reflexivity.
   
   (* case instruction t_i *)
  -destruct (get_first_n_bit l2 8) eqn:Hl3.
   destruct (get_first_n_bit l4 8) eqn:Hl4.
   rewrite  ret_rewrite in H0.
   unfold encode.
   (* inversion H0. *)
   unfold encode_t_n.
   apply commut_equal in H1.
   apply lookdown_encdec in H1.
   inversion H0.
   unfold encode_t_i.
   assert (instr_opcode_t_i
             {|
             instr_opcode_t_i := t;
             instr_operande1_t_i := reg (bit_n l1);
             instr_operande2_t_i := reg (bit_n l3);
             instr_operande3_t_i := imm (bit_n l5) |} = t) by reflexivity.
   rewrite H2.
   rewrite H1.
   assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
   rewrite H4.
   (* these are premliminare assertion to refactor a little bit the code *)
   assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l0 = 24).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H7.
      simpl in H7.
      auto.
     -auto.
   }
   assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l2 = 16).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H9.
      simpl in H9.
      apply get_first_n_bit_size_out in Hl2.
      +destruct Hl2.
       rewrite H11.
       rewrite H6.
       reflexivity.
      +auto.
     -auto.
   }
   assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l4 = 8).
   {
     apply get_first_n_bit_size_out in Hl3.
     destruct Hl3.
     rewrite H11.
     rewrite H8.
     reflexivity.
     exact H9.
   }
   assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
   assert (n_bit 8 (bit_n l) = Some l).
   {
     Check get_first_n_bit_size_out.
     apply get_first_n_bit_size_out in Hl1.
     apply bit_n_bit.
     -destruct Hl1.
     auto.
     -rewrite H.
      repeat apply le_n_S.
      Search (0 <= _).
      apply Peano.le_0_n.
   }
   rewrite H12.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
   rewrite H13.
   assert (instr_operande1_t_i
             {|
             instr_opcode_t_i := t;
             instr_operande1_t_i := reg (bit_n l1);
             instr_operande2_t_i := reg (bit_n l3);
             instr_operande3_t_i := imm (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
   rewrite H14.
   Search operand_to_bin.
   assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
   {
     unfold operand_to_bin.
     apply bit_n_bit.     
     apply get_first_n_bit_size_out in Hl2.
     -destruct Hl2.
      auto.
     -auto.
   }   
   rewrite H15.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
   rewrite H16.
   assert (instr_operande2_t_i
             {|
             instr_opcode_t_i := t;
             instr_operande1_t_i := reg (bit_n l1);
             instr_operande2_t_i := reg (bit_n l3);
             instr_operande3_t_i := imm (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
   rewrite H17.   
   assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl3.
     -destruct Hl3.
      auto.
     -auto.
   }   
   rewrite H18.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
   rewrite H19.
   assert (instr_operande3_t_i
             {|
             instr_opcode_t_i := t;
             instr_operande1_t_i := reg (bit_n l1);
             instr_operande2_t_i := reg (bit_n l3);
             instr_operande3_t_i := imm (bit_n l5) |} = imm (bit_n l5)) by reflexivity.
   rewrite H20.
   assert (operand_to_bin (imm_o (imm (bit_n l5))) = Some l5).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl4.
     destruct Hl4.
     auto.
     auto.
   }   
   rewrite H21.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
   rewrite H22.
   assert (bi = (l ++ l1 ++ l3 ++ l5 ++ l6)). 
   {
     apply get_first_n_bit_res_8 in Hl1.
     apply get_first_n_bit_res_8 in Hl2.
     apply get_first_n_bit_res_8 in Hl3.
     apply get_first_n_bit_res_8 in Hl4.
     rewrite Hl1.
     rewrite Hl2.
     rewrite Hl3.
     rewrite Hl4.
     reflexivity.
   }
   assert (length l6 = 0).
   {
     apply get_first_n_bit_size_out in Hl4.
     -destruct Hl4.
      rewrite H25. rewrite H10. reflexivity.
     -auto.           
   }
   rewrite H23.
   apply length_zero_iff_nil in H24.
   rewrite H24.
   rewrite ret_rewrite.
   rewrite app_nil_r.
   reflexivity.

   (* case d_i *)
  -destruct (get_first_n_bit l2 16) eqn:Hl3.
   rewrite  ret_rewrite in H0.
   unfold encode.
   (* inversion H0. *)
   unfold encode_t_n.
   apply commut_equal in H1.
   apply lookdown_encdec in H1.
   inversion H0.
   unfold encode_d_i.
   assert (instr_opcode_d_i
             {|
             instr_opcode_d_i := t;
             instr_operande1_d_i := reg (bit_n l1);
             instr_operande2_d_i := imm (bit_n l3) |} = t) by reflexivity.   
   rewrite H2.
   rewrite H1.
   assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
   rewrite H4.
   (* these are premliminare assertion to refactor a little bit the code *)
   assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l0 = 24).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H7.
      simpl in H7.
      auto.
     -auto.
   }
   assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l2 = 16).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H9.
      simpl in H9.
      apply get_first_n_bit_size_out in Hl2.
      +destruct Hl2.
       rewrite H11.
       rewrite H6.
       reflexivity.
      +auto.
     -auto.
   }
   assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l4 = 0).
   {
     apply get_first_n_bit_size_out in Hl3.
     destruct Hl3.
     rewrite H11.
     rewrite H8.
     reflexivity.
     rewrite H8.
     reflexivity.
   }
   assert (n_bit 8 (bit_n l) = Some l).
   {
     Check get_first_n_bit_size_out.
     apply get_first_n_bit_size_out in Hl1.
     apply bit_n_bit.
     -destruct Hl1.
     auto.
     -rewrite H.
      repeat apply le_n_S.
      Search (0 <= _).
      apply Peano.le_0_n.
   }
   rewrite H11.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
   rewrite H12.
   assert (instr_operande1_d_i
             {|
             instr_opcode_d_i := t;
             instr_operande1_d_i := reg (bit_n l1);
             instr_operande2_d_i := imm (bit_n l3) |} = reg (bit_n l1)) by reflexivity.
   rewrite H13.
   Search operand_to_bin.
   assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
   {
     unfold operand_to_bin.
     apply bit_n_bit.     
     apply get_first_n_bit_size_out in Hl2.
     -destruct Hl2.
      auto.
     -auto.
   }   
   rewrite H14.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
   rewrite H15.
   assert (instr_operande2_d_i
             {|
             instr_opcode_d_i := t;
             instr_operande1_d_i := reg (bit_n l1);
             instr_operande2_d_i := imm (bit_n l3) |} = imm (bit_n l3)) by reflexivity.
   rewrite H16.   
   assert (operand_to_bin_double (imm_o (imm (bit_n l3))) = Some l3).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl3.
     -destruct Hl3.
      auto.
     -rewrite H8. auto.
   }   
   rewrite H17.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
   rewrite H18.
   assert (bi = (l ++ l1 ++ l3 ++ l4)). 
   {
     apply get_first_n_bit_res_8 in Hl1.
     apply get_first_n_bit_res_8 in Hl2.
     apply get_first_n_bit_res_16 in Hl3.
     rewrite Hl1.
     rewrite Hl2.
     rewrite Hl3.
     reflexivity.
   }
   rewrite H19.
   apply length_zero_iff_nil in H10.
   rewrite H10.
   rewrite ret_rewrite.
   rewrite app_nil_r.
   reflexivity.

  (* case d_n *)
  -destruct (get_first_n_bit l2 16) eqn:Hl3.
   rewrite  ret_rewrite in H0.
   unfold encode.
   (* inversion H0. *)
   unfold encode_t_n.
   apply commut_equal in H1.
   apply lookdown_encdec in H1.
   inversion H0.
   unfold encode_d_n.
   assert (instr_opcode_d_n
             {|
             instr_opcode_d_n := t;
             instr_operande1_d_n := reg (bit_n l1);
             instr_operande2_d_n := reg (bit_n l3) |} = t) by reflexivity.   
   rewrite H2.
   rewrite H1.
   assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
   rewrite H4.
   (* these are premliminare assertion to refactor a little bit the code *)
   assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l0 = 24).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H7.
      simpl in H7.
      auto.
     -auto.
   }
   assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l2 = 16).
   {
     apply get_first_n_bit_size_out in Hl1.
     -destruct Hl1.
      rewrite H in H9.
      simpl in H9.
      apply get_first_n_bit_size_out in Hl2.
      +destruct Hl2.
       rewrite H11.
       rewrite H6.
       reflexivity.
      +auto.
     -auto.
   }
   assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
   assert (length l4 = 0).
   {
     apply get_first_n_bit_size_out in Hl3.
     destruct Hl3.
     rewrite H11.
     rewrite H8.
     reflexivity.
     rewrite H8.
     reflexivity.
   }
   assert (n_bit 8 (bit_n l) = Some l).
   {
     Check get_first_n_bit_size_out.
     apply get_first_n_bit_size_out in Hl1.
     apply bit_n_bit.
     -destruct Hl1.
     auto.
     -rewrite H.
      repeat apply le_n_S.
      Search (0 <= _).
      apply Peano.le_0_n.
   }
   rewrite H11.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
   rewrite H12.
   assert (instr_operande1_d_n
             {|
             instr_opcode_d_n := t;
             instr_operande1_d_n := reg (bit_n l1);
             instr_operande2_d_n := reg (bit_n l3) |} = reg (bit_n l1)) by reflexivity.
   rewrite H13.
   Search operand_to_bin.
   assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
   {
     unfold operand_to_bin.
     apply bit_n_bit.     
     apply get_first_n_bit_size_out in Hl2.
     -destruct Hl2.
      auto.
     -auto.
   }   
   rewrite H14.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
   rewrite H15.
   assert (instr_operande2_d_n
             {|
             instr_opcode_d_n := t;
             instr_operande1_d_n := reg (bit_n l1);
             instr_operande2_d_n := reg (bit_n l3) |} = reg (bit_n l3)) by reflexivity.
   rewrite H16.   
   assert (operand_to_bin_double (reg_o (reg (bit_n l3))) = Some l3).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl3.
     -destruct Hl3.
      auto.
     -rewrite H8. auto.
   }   
   rewrite H17.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
   rewrite H18.
   assert (bi = (l ++ l1 ++ l3 ++ l4)). 
   {
     apply get_first_n_bit_res_8 in Hl1.
     apply get_first_n_bit_res_8 in Hl2.
     apply get_first_n_bit_res_16 in Hl3.
     rewrite Hl1.
     rewrite Hl2.
     rewrite Hl3.
     reflexivity.
   }
   rewrite H19.
   apply length_zero_iff_nil in H10.
   rewrite H10.
   rewrite ret_rewrite.
   rewrite app_nil_r.
   reflexivity.
Qed.
   
  
   
   
   
  