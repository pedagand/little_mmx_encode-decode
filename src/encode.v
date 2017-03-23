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

Definition operand_to_bin_double (o : operande) : option (list bool) :=
  match o with
  | imm_o (imm k) => n_bit 16 k
  | reg_o (reg k) => n_bit 16 k
  end.

(* -----------------------------------now for instr_operande_t_n ----------------------------------*)
Lemma operand_to_bin_hypothesis1_t_n : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande1_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande1_t_n).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande1_t_n i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_hypothesis2_t_n : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande2_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande2_t_n).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande2_t_n i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_hypothesis3_t_n : forall (l : list bool) (i : instruction_tern_n),
    operand_to_bin (reg_o (instr_operande3_t_n i)) = Some l -> reg (bit_n l) = i.(instr_operande3_t_n).
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande3_t_n i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.




(* -----------------------------------now for instr_operande_t_i ----------------------------------*)
Lemma operand_to_bin_hypothesis1_t_i : forall (l : list bool) (i : instruction_tern_i),
    operand_to_bin (reg_o (instr_operande1_t_i i)) = Some l -> reg (bit_n l) = i.(instr_operande1_t_i).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande1_t_i i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_hypothesis2_t_i : forall (l : list bool) (i : instruction_tern_i),
    operand_to_bin (reg_o (instr_operande2_t_i i)) = Some l -> reg (bit_n l) = i.(instr_operande2_t_i).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande2_t_i i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_hypothesis3_t_i : forall (l : list bool) (i : instruction_tern_i),
    operand_to_bin (imm_o (instr_operande3_t_i i)) = Some l -> imm (bit_n l) = i.(instr_operande3_t_i).
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande3_t_i i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.



(* -----------------------------------now for instr_operande_d_n ----------------------------------*)
Lemma operand_to_bin_hypothesis1_d_n : forall (l : list bool) (i : instruction_duo_n),
    operand_to_bin (reg_o (instr_operande1_d_n i)) = Some l -> reg (bit_n l) = i.(instr_operande1_d_n).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande1_d_n i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_double_hypothesis2_d_n : forall (l : list bool) (i : instruction_duo_n),
    operand_to_bin_double (reg_o (instr_operande2_d_n i)) = Some l -> reg (bit_n l) = i.(instr_operande2_d_n).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande2_d_n i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.



(* -----------------------------------now for instr_operande_d_i ----------------------------------*)
Lemma operand_to_bin_hypothesis1_d_i : forall (l : list bool) (i : instruction_duo_i),
    operand_to_bin (reg_o (instr_operande1_d_i i)) = Some l -> reg (bit_n l) = i.(instr_operande1_d_i).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande1_d_i i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.
Lemma operand_to_bin_double_hypothesis2_d_i : forall (l : list bool) (i : instruction_duo_i),
    operand_to_bin_double (imm_o (instr_operande2_d_i i)) = Some l -> imm (bit_n l) = i.(instr_operande2_d_i).
Proof.
  intros.
  unfold operand_to_bin in H.
  destruct (instr_operande2_d_i i).
  apply n_bit_n in H.
  rewrite H.
  reflexivity.
Qed.


(* -----------------------------------Other operand_to_bin lemma ----------------------------------*)
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

Lemma operand_to_bin_double_size : forall (o : operande) (l : list bool),
    operand_to_bin_double o = Some l -> length l = 16.
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
Fixpoint get_first_n_bit  (bi : list bool) (size : nat) : (list bool*list bool) :=
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

Lemma get_first_n_bit_size_nil_n : forall (n : nat) (l : list bool), length l = n -> get_first_n_bit l n= (l,[]).
Proof.
  induction n.
  -intros.
   Search (length _ = 0).
   apply length_zero_iff_nil in H.
   rewrite H.
   reflexivity.
  -intros.
   unfold get_first_n_bit.
   destruct l.
   +reflexivity.
   +fold get_first_n_bit.
    assert (get_first_n_bit l n = (l,[])) by (apply IHn; auto).
    rewrite H0.
    reflexivity.
Qed.
    
Lemma get_first_n_bit_size_tl : forall  (n : nat) (l : list bool) (tl : list bool), length l = n -> get_first_n_bit (l ++ tl) n = (l,tl).
Proof.
  induction n.
  -intros.
   apply length_zero_iff_nil in H.
   rewrite H.
   simpl.
   destruct tl.
   +reflexivity.
   +reflexivity.
  -intros.
   unfold get_first_n_bit.
   destruct l.
   fold get_first_n_bit.
   +discriminate.
   +simpl.
    fold get_first_n_bit.
    assert (get_first_n_bit (l ++ tl) n = (l,tl)).
    {
      apply IHn.
      simpl in H.
      inversion H.
      reflexivity.
    }
    rewrite H0.
    reflexivity.   
Qed.
  

Lemma get_first_n_bit_size_4 : forall (l1 l2 l3 l4 : list bool),
    length l1 = 8 -> get_first_n_bit (l1 ++ l2 ++ l3 ++ l4) 8 = (l1,l2 ++ l3 ++ l4).
Proof.
  intros.
  specialize (get_first_n_bit_size_tl 8 l1 (l2 ++ l3 ++ l4)).
  intros.  
  auto.  
Qed.

Lemma get_first_n_bit_size_3 : forall (n : nat) (l1 l2 l3 : list bool),
    length l1 = n -> get_first_n_bit (l1 ++ l2 ++ l3) n = (l1,l2 ++ l3).
Proof.
  intros.
  specialize (get_first_n_bit_size_tl n l1 (l2 ++ l3)).
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

(* theese are the encode functions for the different type of instruction *)

Definition encode_t_n (i : instruction_tern_n) : option binary_instruction :=
  let! k := lookup (tag_t_n (i.(instr_opcode_t_n))) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin (reg_o i.(instr_operande1_t_n)) in 
                       fun o1 => let! o2 := operand_to_bin (reg_o i.(instr_operande2_t_n)) in
                                 fun o2 => let! o3 := operand_to_bin (reg_o i.(instr_operande3_t_n)) in
                                           fun o3 => ret (code ++ o1 ++ o2 ++ o3).

Definition encode_t_i (i : instruction_tern_i) : option binary_instruction :=
  let! k := lookup (tag_t_i (i.(instr_opcode_t_i))) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin (reg_o i.(instr_operande1_t_i)) in 
                       fun o1 => let! o2 := operand_to_bin (reg_o i.(instr_operande2_t_i)) in
                                 fun o2 => let! o3 := operand_to_bin (imm_o i.(instr_operande3_t_i)) in
                                           fun o3 => ret (code ++ o1 ++ o2 ++ o3).

Definition encode_d_n (i : instruction_duo_n) : option binary_instruction :=
  let! k := lookup (tag_d_n (i.(instr_opcode_d_n))) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin (reg_o i.(instr_operande1_d_n)) in 
                       fun o1 => let! o2 := operand_to_bin_double (reg_o i.(instr_operande2_d_n)) in
                                 fun o2 => ret (code ++ o1 ++ o2).

Definition encode_d_i (i : instruction_duo_i) : option binary_instruction :=
  let! k := lookup (tag_d_i (i.(instr_opcode_d_i))) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin (reg_o i.(instr_operande1_d_i)) in 
                       fun o1 => let! o2 := operand_to_bin_double (imm_o i.(instr_operande2_d_i)) in
                                 fun o2 => ret (code ++ o1 ++ o2).



(* now the general encode function which take a general instruction *)

Definition encode (i : instruction) : option binary_instruction :=
  match i with
  | instr_t_n t => encode_t_n t
  | instr_t_i t => encode_t_i t
  | instr_d_n t => encode_d_n t
  | instr_d_i t => encode_d_i t
  end.
  


  (* flux d'instruction il faut faire une fonction qui decode le debut de la liste et retourne la suite de la liste *)

(* this is the decode function (with this one we only need one general function) *)
Definition decode (bi : binary_instruction) : option instruction :=
  match get_first_n_bit bi 8 with
  | (li,next) => let! t := lookdown (bit_n li) encdec in
                 fun t => match get_first_n_bit next 8 with
                          | (op1,next) =>
                            match t with
                            | tag_t_n tn => match get_first_n_bit next 8 with
                                            | (op2,next) => match get_first_n_bit next 8 with
                                                            | (op3,next) => 
                                                              ret (instr_t_n (mk_instr_t_n tn
                                                                                           (reg (bit_n op1))
                                                                                           (reg (bit_n op2))
                                                                                           (reg (bit_n op3))))
                                                            end
                                            end
                            | tag_t_i ti => match get_first_n_bit next 8 with
                                          | (op2,next) => match get_first_n_bit next 8 with
                                                          | (op3,next) => 
                                                            ret (instr_t_i (mk_instr_t_i ti
                                                                                         (reg (bit_n op1))
                                                                                         (reg (bit_n op2))
                                                                                         (imm (bit_n op3))))
                                                          end
                                            end
                            | tag_d_i di => match get_first_n_bit next 16 with
                                            | (op2,next) => 
                                              ret (instr_d_i (mk_instr_d_i di
                                                                           (reg (bit_n op1))
                                                                           (imm (bit_n op2))))
                                            end
                                          | tag_d_n dn => match get_first_n_bit next 16 with
                                                          | (op2,next) => 
                                                            ret (instr_d_n (mk_instr_d_n dn
                                                                                         (reg (bit_n op1))
                                                                                         (reg (bit_n op2))))
                                                          end
                            end
                          end
  end.


                            






(* little test (this is the end of the file) *)


Definition my_instr := (mk_instr_t_n AND (reg 10) (reg 11) (reg 12)).


Definition my_instr_encoded_decoded' := match encode_t_n my_instr with
                                      | Some lol => decode lol
                                      | None => None
                                       end. 


