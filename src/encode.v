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
    | imm_o (imm k) => n_bit 8 (k mod 256)
    | reg_o (reg k) => n_bit 8 (k mod 256)
  end.

Lemma operand_to_bin_never_fail : forall (o : operande), exists (l : list bool), operand_to_bin o = Some l.
Proof.
  intros.
  (* assert (forall (n : nat), n mod 256 <? 2 ^ 8 = true). *)
  (* { *)
    assert (forall (n : nat), n mod 256 < 2 ^ 8).
    {
      assert (2 ^ 8 = 256) by reflexivity.
      rewrite H.
      (* i need something of the form  "_ mod n < n" *)
      Check Nat.mod_bound_pos.
      intros n.
      apply Nat.mod_bound_pos.
      Search (0 <= _).
      apply Peano.le_0_n.
      Search (0 < S _).
      apply Nat.lt_0_succ.
    }
    (* SearchAbout (_ < _). *)
    (* intros. *)
    (* specialize (Nat.ltb_spec0 (n mod 256) (2 ^ 8)). *)
    (* intros. *)
    (* apply reflect_iff in H0. *)
    (* rewrite iff_to_and in H0. *)
    (* destruct H0. *)
    (* apply H0. *)
    (* specialize (H n). *)
    (* exact H. *)
  (* }  *)
  destruct o.
  -unfold operand_to_bin.
   destruct i.
   apply n_bit_dont_fail.
   specialize (H n).
   exact H.
  -unfold operand_to_bin.
   destruct r.
   apply n_bit_dont_fail.
   specialize (H n).
   exact H.
Qed.



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


Lemma get_first_n_bit_size : forall (l : list bool) (n : nat), length l = n -> get_first_n_bit l n = (l,[]).
Proof.
  intros.
  Admitted.

Lemma get_first_n_bit_size_tl : forall (l : list bool) (tl : list bool), length l = 8 -> get_first_n_bit (l ++ tl) 8 = (l,tl).
Proof.
  intros.
  induction tl.
  -rewrite app_nil_r.
   apply get_first_n_bit_size.
   exact H.
Admitted.


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
                                                         
(* Definition encode (i : instruction) : option binary_instruction :=   *)
(*   let! k := lookup i.(instr_opcode) encdec in *)
(*   fun k => let! code := n_bit 8 k in *)
(*            fun code => let! o1 := operand_to_bin i.(instr_operande1) in  *)
(*                        fun o1 => let! o2 := operand_to_bin i.(instr_operande2) in *)
(*                                  fun o2 =>                                             *)
(*                                                let! o3 := compute_op3 i in                                               *)
(*                                                fun o3 => ret (code ++ o1 ++ o2 ++ o3). *)


(* Theorem encode_size : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> length bi = 32. *)
(* Proof. *)
(*   intros. *)
(*   unfold encode in H. *)
(*   intros. *)
(*   unfold encode in H. *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   Search operand_to_bin. *)
(*   apply commut_equal in H4. *)
(*   apply commut_equal in H3. *)
(*   apply commut_equal in H2. *)
(*   apply commut_equal in H1. *)
(*   apply commut_equal in H0. *)
(*   apply operand_to_bin_size in H3. *)
(*   apply operand_to_bin_size in H2. *)
(*   assert (keep : lookup (instr_opcode i) encdec = Some x) by auto. *)
(*   assert (forall (t : tag) (n : nat), lookup t encdec = Some n -> n <= 3) by admit. *)
(*   apply H5 in H0. *)
(*   Search n_bit. *)
(*   Check size_n_bit. *)
(*   apply size_n_bit in H1. *)
(*   apply compute_op3_size in H4. *)
(*   assert (length x0 = 8 -> length x1 = 8 -> length x2 = 8 -> length x3 = 8 -> length (x0 ++ x1 ++ x2 ++ x3) = 32). *)
(*   { *)
(*     intros. *)
(*     Search length. *)
(*     Check app_length. *)
(*     repeat (rewrite app_length). *)
(*     rewrite H6. *)
(*     rewrite H7. *)
(*     rewrite H8. *)
(*     rewrite H9. *)
(*     reflexivity. *)
(*   } *)
(*   rewrite ret_rewrite in H. *)
(*   inversion H. *)
(*   auto. *)
(* Admitted. *)

(* Definition encode_mytho (i : instruction) : option (list bool) := *)
(*   let! bo1 := lookup i.(instr_opcode) encdec in *)
(*   fun bo1 => (n_bit 8 bo1). *)

(* Definition decode_mytho (bi : list bool) : option tag := *)
(*   match get_first_n_bit bi 8 with *)
(*   | (h,tl) => lookdown (bit_n h) encdec *)
(*   end. *)

(* Definition my_instr_encoded_decoded := match encode_mytho my_instr with *)
(*                                       | Some lol => decode_mytho lol *)
(*                                       | None => None *)
(*                                        end. *)

(* Compute my_instr_encoded_decoded. *)

(* Theorem test_theorem_mytho : forall (i : instruction) (bi : list bool), *)
(*     encode_mytho i = Some bi -> decode_mytho bi = Some i.(instr_opcode). *)
(* Proof. *)
(*   intros i bi H. *)
(*   unfold encode_mytho in H.   *)
(*   apply bind_rewrite in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   unfold decode_mytho. *)
(*   assert (length bi = 8 -> get_first_n_bit bi 8 = (bi,[])). *)
(*   { *)
(*     intros. *)
(*     admit. *)
(*   } *)
(*   assert (keep : n_bit 8 x = Some bi) by auto. *)
(*   Check operand_to_bin_size. *)
(*   specialize size_n_bit. *)
(*   intros.   *)
(*   apply H2 in H. *)
(*   apply H1 in H. *)
(*   rewrite H. *)
(*   Search lookdown. *)
(*   apply lookdup_encdec. *)
(*   unfold lookdown. *)
(*   assert (n_bit 8 x = Some bi -> bit_n bi = x). *)
(*   { *)
(*     intros. *)
(*     Search n_bit. *)
(*     specialize (n_bit_n bi 8 x). *)
(*     intros. *)
(*     apply H4 in H3. *)
(*     exact H3. *)
(*   } *)
(*   rewrite H3. *)
(*   -apply commut_equal. *)
(*    exact H0. *)
(*   -exact keep. *)
(* Admitted. *)
  
  
  





(* this is test purpose *)
(* Definition encode_mytho (i : instruction) : option binary_instruction := *)
(*   let! bo1 := operand_to_bin i.(instr_operande1) in *)
(*   fun bo1 => ret bo1. *)

(* Definition decode_mytho (bi : binary_instruction) : option instruction := *)
(*   match get_first_n_bit with *)
(*   | (h,tl) => bit_n h  *)

(* Print operand_to_bin. *)

(* Lemma test_proof : forall (i : instruction) (l : list bool) (bi : binary_instruction), encode_mytho i = Some bi -> length bi = 8. *)
(* Proof. *)
(*   intros. *)
(*   unfold encode_mytho in H. *)
(*   Check bind_rewrite. *)
(*   specialize bind_rewrite. *)
(*   intros. *)
(*   apply H0 in H. *)
(*   destruct H. *)
(*   destruct H. *)
(*   specialize (ret_rewrite (list bool)). *)
(*   intros. *)
(*   rewrite H2 in H. *)
(*   inversion H. *)
(*   specialize (commut_equal (option (list bool))). *)
(*   intros. *)
(*   apply H3 in H1. *)
(*   Check operand_to_bin_size. *)
(*   apply operand_to_bin_size in H1.   *)
(*   rewrite <- H4. *)
(*   exact H1. *)
(* Qed. *)





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


                                                                            

Definition decode (bi : binary_instruction) : option instruction :=
  match get_first_n_bit bi 8 with
  | (li,next) => let! t := lookdown (bit_n li) encdec in
                 fun t => match get_first_n_bit next 8 with
                          | (op1,next) => match get_first_n_bit next 8 with
                                          | (op2,next) => match get_first_n_bit next 8 with
                                                          | (op3,next) => match t with
                                                                          | tag_n tn => Some (mk_instr t
                                                                                                       (reg (bit_n op1))
                                                                                                       (reg (bit_n  op2))
                                                                                                       (reg (bit_n  op3)))
                                                                          | tag_i ti => Some (mk_instr t
                                                                                                       (reg (bit_n op1))
                                                                                                       (reg (bit_n op2))
                                                                                                       (immediate (bit_n op3)))
                                                                          end
                                                          end
                                          end
                          end
  end.


Print my_instr.
Definition my_instr_encoded_decoded' := match encode my_instr with
                                      | Some lol => decode lol
                                      | None => None
                                       end.
Print my_instr.
Compute my_instr_encoded_decoded.

Check instruction.




Theorem encode_decode : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i.
Proof.
  assert (I: forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i).
  {
    intros.
    unfold encode in H.
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
    Check get_first_n_bit_size_tl.
    Search ret.
    rewrite ret_rewrite in H.
    inversion H.
    Check get_first_n_bit_size_tl.
    assert (length x0 = 8 -> get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0, x1 ++ x2 ++ x3)) by admit.    
    unfold decode.
    rewrite H5.
    -{
        apply commut_equal in H0.
        apply lookdup_encdec in H0.
        Search n_bit.
        Check bit_n_bit.
        apply commut_equal in H1.
        apply n_bit_n in H1.
        rewrite H1.
        rewrite H0.
        assert (forall (f : tag -> option instruction), bind (Some (instr_opcode i)) f = f (instr_opcode i)) by reflexivity.
        rewrite H7.
        assert(get_first_n_bit (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by admit.
        rewrite H8.
        assert(get_first_n_bit (x2 ++ x3) 8 = (x2,x3)) by admit.
        rewrite H9.
        assert(get_first_n_bit x3 8 = (x3,[])) by admit.
        rewrite H10.
        destruct (instr_opcode i).        
        -{
            admit.
          }
        -
  }
Admitted.





Lemma encode_decode : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> decode bi = Some i.
Proof.
  (* why can't i write this ? *)
(*   assert (I : forall (i : instruction) (bi : binary_instruction), encode i = Some bi ->
                                                                  lookdown (bit_n (cut_binary_instruction bi 0 8)) = (i.instr_opcode)). *)
  induction i.
  unfold encode.

  
  
Admitted.





Example test_instr := mk_instr (tag_i ADD_I) (reg 10) (reg 11) (immediate 12).
Compute encode test_instr.
Definition testBoolList := [false; true; false; false; false; false; false; false; false; true; false; true; false; false; false; false; true; true; false; true; false; false; false; false; false; false; true; true; false; false; false; false].
Compute length testBoolList.

encode test_instr

Compute (match encode test_instr with | Some i => decode i | None => None end).
  




