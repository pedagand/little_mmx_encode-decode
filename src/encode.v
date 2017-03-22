Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list.

Require Import Mmx.ast_instructions.
Require Import Mmx.binary.

Check n_bit_dont_fail.

(* (* functions to encode decode instructions *) *)
(* (* TODO :: Here this function can't be call for immediate *) *)
Definition operand_to_bin (o : operande) : option (list bool) :=
  match o with
    | imm_o (imm k) => n_bit 8 k
    | reg_o (reg k) => n_bit 8 k
  end.

(* Lemma operand_to_bin_never_fail : forall (o : operande), exists (l : list bool), operand_to_bin o = Some l. *)
(* Proof. *)
(*   intros. *)
(*   (* assert (forall (n : nat), n mod 256 <? 2 ^ 8 = true). *) *)
(*   (* { *) *)
(*     assert (forall (n : nat), n mod 256 < 2 ^ 8). *)
(*     { *)
(*       assert (2 ^ 8 = 256) by reflexivity. *)
(*       rewrite H. *)
(*       (* i need something of the form  "_ mod n < n" *) *)
(*       Check Nat.mod_bound_pos. *)
(*       intros n. *)
(*       apply Nat.mod_bound_pos. *)
(*       Search (0 <= _). *)
(*       apply Peano.le_0_n. *)
(*       Search (0 < S _). *)
(*       apply Nat.lt_0_succ. *)
(*     } *)
(*     (* SearchAbout (_ < _). *) *)
(*     (* intros. *) *)
(*     (* specialize (Nat.ltb_spec0 (n mod 256) (2 ^ 8)). *) *)
(*     (* intros. *) *)
(*     (* apply reflect_iff in H0. *) *)
(*     (* rewrite iff_to_and in H0. *) *)
(*     (* destruct H0. *) *)
(*     (* apply H0. *) *)
(*     (* specialize (H n). *) *)
(*     (* exact H. *) *)
(*   (* }  *) *)
(*   destruct o. *)
(*   -unfold operand_to_bin. *)
(*    destruct i. *)
(*    apply n_bit_dont_fail. *)
(*    specialize (H n). *)
(*    exact H. *)
(*   -unfold operand_to_bin. *)
(*    destruct r. *)
(*    apply n_bit_dont_fail. *)
(*    specialize (H n). *)
(*    exact H. *)
(* Qed. *)
(* SearchAbout bit_n. *)
Lemma operand_to_bin_hypothesis1 : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande1_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande1_t_n).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande1_t_n i).
  Search n_bit.
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.

Lemma operand_to_bin_hypothesis2 : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande2_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande2_t_n).
Admitted.

Lemma operand_to_bin_hypothesis3 : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande3_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande3_t_n).
Admitted.

Lemma operand_to_bin_size : forall (o : operande) (l : list bool),
    operand_to_bin o = Some l -> length l = 8.
Proof.
  destruct o.
  -unfold operand_to_bin.
   intros l H.
   destruct i in H.
   apply size_n_bit in H.
   rewrite H.
   reflexivity.
   -unfold operand_to_bin.
    intros l H.
    destruct r in H.
    apply size_n_bit in H.
    rewrite H.
    reflexivity.
Qed.





(* HERE i don't make any garantee about the result if the binary_instruction is to small but i will have some lemma to give it *)
Fixpoint get_first_n_bit (bi : list bool) (size : nat) : (list bool*list bool) :=
  match size with
  | 0 => ([],bi)
  | S n => match bi with
           | h :: tl => match get_first_n_bit tl n with
                        | (l1,l2) => (h :: l1,l2)
                        end
           | [] => ([],[])
           end
  end.
Definition testList := [true ; false ; true ; false ; false ; false ; true ; true ].
Definition testList' := [true ; false ; true].
Compute get_first_n_bit testList' 3.
Compute get_first_n_bit testList' 4.


Lemma get_first_n_bit_size_nil_n : forall (n : nat) (l : list bool), length l = n -> get_first_n_bit l n = (l,[]).
Proof.
  induction n.
  -intros.
   Search (length _ = 0).
   apply length_zero_iff_nil in H.
   rewrite H.
   reflexivity.
  -intros.
   Search (length _ = S _).
Admitted.
   
 

Lemma get_first_n_bit_size_tl : forall (tl : list bool) (l : list bool), length l = 8 -> get_first_n_bit (l ++ tl) 8 = (l,tl).
Proof.
  induction tl.
  -intros.
   rewrite app_nil_r.
   apply get_first_n_bit_size_nil_n.
   exact H.
  -
Admitted.
  

Lemma get_first_n_bit_size_4 : forall (l1 l2 l3 l4 : list bool),
    length l1 = 8 -> get_first_n_bit (l1 ++ l2 ++ l3 ++ l4) 8 = (l1,l2 ++ l3 ++ l4).
Proof.
  intros.
  specialize (get_first_n_bit_size_tl (l2 ++ l3 ++ l4) l1).
  intros.
  auto.
Qed.
Lemma get_first_n_bit_size_3 : forall (l1 l2 l3 : list bool),
    length l1 = 8 -> get_first_n_bit (l1 ++ l2 ++ l3) 8 = (l1,l2 ++ l3).
Proof.
  intros.
  specialize (get_first_n_bit_size_tl (l2 ++ l3) l1).
  intros.
  auto.
Qed.




(* Lemma get_first_n_bit_size : forall (bi : list bool) (size : nat), n < (length bi) -> get_first_n_bit bi n = ( *)



Definition M A := option A.

Definition ret {A} (a : A) : M A := Some a.

Lemma ret_rewrite : forall (A : Type) (a : A), ret a = Some a.
Proof. intros. unfold ret. reflexivity. Qed.

Definition bind {A B} (ma : M A)(k : A -> M B): M B :=
  match ma with
  | Some a => k a
  | None => None
  end.
Check bind.


Lemma bind_rewrite : forall (A B : Type) (ma : M A) (k : A -> M B) (res : B), bind ma k = Some res -> exists (a : A), k a = Some res /\ Some a = ma.
  intros.
  remember ma.
  destruct m.
  -exists a.
   split.
   +rewrite <- H.
    reflexivity.
   +reflexivity.
  -simpl in H.
   discriminate.
Qed.


(* TODO :: to delete but can't find this theorem so proof of it *)
Lemma commut_equal : forall (A : Type) (a b : A), a = b -> b = a.
Proof.
  intros. rewrite H. reflexivity. Qed.





Notation "'let!' x ':=' ma 'in' k" := (bind ma k) (at level 30). 



(* TODO :: here i know that i can always get a binary_instruction but some function don't allow me to  *)
(* return a binary_instruction without encapsulate it into an option type *)

Definition encode_t_n (i : instruction_tern_n) : option binary_instruction :=
  let! k := lookup (tag_t_n (i.(instr_opcode_t_n))) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin (reg_o i.(instr_operande1_t_n)) in 
                       fun o1 => let! o2 := operand_to_bin (reg_o i.(instr_operande2_t_n)) in
                                 fun o2 => let! o3 := operand_to_bin (reg_o i.(instr_operande3_t_n)) in
                                           fun o3 => ret (code ++ o1 ++ o2 ++ o3).
                                                         


  (* flux d'instruction il faut faire une fonction qui decode le debut de la liste et retourne la suite de la liste *)

Definition decode (bi : binary_instruction) : option instruction :=
  match get_first_n_bit bi 8 with
  | (li,next) => let! t := lookdown (bit_n li) encdec in
                 fun t => match get_first_n_bit next 8 with
                          | (op1,next) => match get_first_n_bit next 8 with
                                          | (op2,next) => match get_first_n_bit next 8 with
                                                          | (op3,next) => match t with
                                                                          | tag_t_n tn =>
                                                                            ret (instr_t_n (mk_instr_t_n tn
                                                                                         (reg (bit_n op1))
                                                                                         (reg (bit_n op2))
                                                                                         (reg (bit_n op3))))
                                                                          | tag_t_i ti =>
                                                                            ret (instr_t_i (mk_instr_t_i ti
                                                                                         (reg (bit_n op1))
                                                                                         (reg (bit_n op2))
                                                                                         (imm (bit_n op3))))
                                                                          | tag_d_i di =>
                                                                            ret (instr_d_i (mk_instr_d_i di
                                                                                         (reg (bit_n op1))
                                                                                         (imm (bit_n (op2 ++ op3)))))
                                                                          | tag_d_n dn =>
                                                                            ret (instr_d_n (mk_instr_d_n dn
                                                                                         (reg (bit_n op1))
                                                                                         (reg (bit_n (op2 ++ op3)))))
                                                                          end
                                                          end
                                          end
                          end
  end.



Definition my_instr := (mk_instr_t_n AND (reg 10) (reg 11) (reg 12)).


Definition my_instr_encoded_decoded' := match encode_t_n my_instr with
                                      | Some lol => decode lol
                                      | None => None
                                       end. 
Print my_instr.
Compute my_instr_encoded_decoded'.

(* this is an important thinking i have to try to find this relation into my proof *)
(* Lemma decode_rewrite_inst_t_n : forall (i : instruction_tern_n) (bi : binary_instruction), *)
(*     decode bi = Some (instr_t_n i) -> i.(instr_opcode_t_n) = (lookdown (bit_n (get_first_n_bit bi 8)) encdec). *)


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

(* Lemma encode_decode_t_n : forall (i : instruction_tern_n) (bi : binary_instruction), *)
(*     encode_t_n i = Some bi -> decode bi = Some (instr_t_n i). *)



Check instruction.




(* Theorem encode_decode : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i. *)
(* Proof. *)
(*   assert (I: forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i). *)
(*   { *)
(*     intros. *)
(*     unfold encode in H. *)
(*     apply bind_rewrite in H. *)
(*     destruct H. *)
(*     destruct H. *)
(*     apply bind_rewrite in H. *)
(*     destruct H. *)
(*     destruct H. *)
(*     apply bind_rewrite in H. *)
(*     destruct H. *)
(*     destruct H. *)
(*     apply bind_rewrite in H. *)
(*     destruct H. *)
(*     destruct H. *)
(*     apply bind_rewrite in H. *)
(*     destruct H. *)
(*     destruct H. *)
(*     Check get_first_n_bit_size_tl. *)
(*     Search ret. *)
(*     rewrite ret_rewrite in H. *)
(*     inversion H. *)
(*     Check get_first_n_bit_size_tl. *)
(*     assert (length x0 = 8 -> get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0, x1 ++ x2 ++ x3)) by admit.     *)
(*     unfold decode. *)
(*     rewrite H5. *)
(*     -{ *)
(*         apply commut_equal in H0. *)
(*         apply lookdup_encdec in H0. *)
(*         Search n_bit. *)
(*         Check bit_n_bit. *)
(*         apply commut_equal in H1. *)
(*         apply n_bit_n in H1. *)
(*         rewrite H1. *)
(*         rewrite H0. *)
(*         assert (forall (f : tag -> option instruction), bind (Some (instr_opcode i)) f = f (instr_opcode i)) by reflexivity. *)
(*         rewrite H7. *)
(*         assert(get_first_n_bit (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by admit. *)
(*         rewrite H8. *)
(*         assert(get_first_n_bit (x2 ++ x3) 8 = (x2,x3)) by admit. *)
(*         rewrite H9. *)
(*         assert(get_first_n_bit x3 8 = (x3,[])) by admit. *)
(*         rewrite H10. *)
(*         destruct (instr_opcode i).         *)
(*         -{ *)
(*             admit. *)
(*           } *)
(*         - *)
(*   } *)
(* Admitted. *)





(* Lemma encode_decode : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i. *)
(* Proof. *)
(*   (* why can't i write this ? *) *)
(* (*   assert (I : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> *)
(*                                                                   lookdown (bit_n (cut_binary_instruction bi 0 8)) = (i.instr_opcode)). *) *)
(*   induction i. *)
(*   unfold encode. *)

  
  
(* Admitted. *)





(* Example test_instr := mk_instr (tag_i ADD_I) (reg 10) (reg 11) (immediate 12). *)
(* Compute encode test_instr. *)
(* Definition testBoolList := [false; true; false; false; false; false; false; false; false; true; false; true; false; false; false; false; true; true; false; true; false; false; false; false; false; false; true; true; false; false; false; false]. *)
(* Compute length testBoolList. *)

(* encode test_instr *)

(* Compute (match encode test_instr with | Some i => decode i | None => None end). *)
  




