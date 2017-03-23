Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.


Lemma get_first_n_bit_res : forall (n : nat) (l l1 l2 : list bool), (get_first_n_bit l n = (l1, l2) -> l = l1 ++ l2).
Proof.
  induction n.
  -intros.
   destruct l.
   +simpl in H.
    inversion H.
    reflexivity.
   +simpl in H.
    inversion H.
    reflexivity.
  -intros.
Admitted.
  


Lemma get_first_n_bit_with_size : forall (bi li tl: list bool) , length bi = 32 -> get_first_n_bit bi 8 = (li,tl) -> length li = 8 /\ length tl = 24.
Proof.
  intros.
  Search get_first_n_bit.
Admitted.


Lemma get_first_n_bit_size_out : forall (n : nat) (bi l l0 : list bool),
    get_first_n_bit bi n = (l, l0) -> length l = n /\ length l0 = (length bi) - n.
Proof.
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
   assert (n_bit 8 (bit_n l) = Some l).
   {
     Check get_first_n_bit_size_out.
     apply get_first_n_bit_size_out in Hl1.
     apply bit_n_bit.
     destruct Hl1.
     auto.
   }
   rewrite H6.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
   rewrite H7.
   assert (instr_operande1_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
   rewrite H8.
   Search operand_to_bin.
   assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl2.
     destruct Hl2.
     auto.
   }
   rewrite H9.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
   rewrite H10.
   assert (instr_operande2_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
   rewrite H11.
   assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl3.
     destruct Hl3.
     auto.
   }
   rewrite H12.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
   rewrite H13.
   assert (instr_operande3_t_n
             {|
             instr_opcode_t_n := t;
             instr_operande1_t_n := reg (bit_n l1);
             instr_operande2_t_n := reg (bit_n l3);
             instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l5)) by reflexivity.
   rewrite H14.
   assert (operand_to_bin (reg_o (reg (bit_n l5))) = Some l5).
   {
     unfold operand_to_bin.
     apply bit_n_bit.
     apply get_first_n_bit_size_out in Hl4.
     destruct Hl4.
     auto.
   }   
   rewrite H15.
   assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
   rewrite H16.
   assert (bi = (l ++ l1 ++ l3 ++ l5 ++ l6)). 
   {
     apply get_first_n_bit_res in Hl1.
     apply get_first_n_bit_res in Hl2.
     apply get_first_n_bit_res in Hl3.
     apply get_first_n_bit_res in Hl4.
     rewrite Hl1.
     rewrite Hl2.
     rewrite Hl3.
     rewrite Hl4.
     reflexivity.
   }
   assert (l6 = []).
   {
     Search (get_first_n_bit).
     apply get_first_n_bit_size_out in Hl1.
     apply get_first_n_bit_size_out in Hl2.
     apply get_first_n_bit_size_out in Hl3.
     apply get_first_n_bit_size_out in Hl4.
     destruct Hl1.
     destruct Hl2.
     destruct Hl3.
     destruct Hl4.
     rewrite H23 in H25.
     rewrite H21 in H25.
     rewrite H19 in H25.
     rewrite H in H25.
     simpl in H25.
     Search (length _ = 0).
     apply length_zero_iff_nil in H25.
     auto.
   }
   rewrite H17.
   rewrite H18.
   rewrite ret_rewrite.
   rewrite app_nil_r.
   reflexivity.
   
  -admit.
   Admitted.
   
  
   
   
   
  