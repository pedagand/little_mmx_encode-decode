Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list.

Require Import Mmx.ast_instructions.
Require Import Mmx.binary.



(* functions to encode decode instructions *)
(* TODO :: here is that the good reasoning about empty *)
Definition operand_to_bin (o : operand) : option (list bool) :=
  match o with
    | immediate k => n_bit 8 k
    | reg k => n_bit 8 k
    | empty => n_bit 8 0
  end.
Definition bin_to_operand (l : list bool) : operand :=
  match bit_n l with
  | 0 => empty
  | n => reg n
  end.
    


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




Definition M A := option A.

Definition ret {A} (a : A) : M A := Some a.

Definition bind {A B} (ma : M A)(k : A -> M B): M B :=
  match ma with
  | Some a => k a
  | None => None
  end.
Check bind.
  

Notation "'let!' x ':=' ma 'in' k" := (bind ma k) (at level 30). 

Definition is_op_immediate (t : tag) : bool :=
  match t with
  | tag_i _ => true
  | _ => false
  end.
Definition is_immediate (op : operand) : bool :=
  match op with
  | immediate _ => true
  | _ => false
  end.

Print negb.

Definition is_valide_immediate (t : tag) (op : operand) : bool :=
  if is_op_immediate t then is_immediate op else negb (is_immediate op).

(* TODO :: here i know that i can always get a binary_instruction but some function don't allow me to  *)
(* return a binary_instruction without encapsulate it into an option type *)
Definition encode (i : instruction) : option binary_instruction :=
  if is_valide_immediate i.(instr_opcode) i.(instr_operande3) then 
  let! k := lookup i.(instr_opcode) encdec in
  fun k => let! code := n_bit 8 k in
           fun code => let! o1 := operand_to_bin i.(instr_operande1) in 
                       fun o1 => let! o2 := operand_to_bin i.(instr_operande2) in
                                 fun o2 =>                                            
                                               let! o3 := operand_to_bin i.(instr_operande3) in                                              
                                               fun o3 => ret (code ++ o1 ++ o2 ++ o3)
  else None.

Definition encode_mytho (i : instruction) : option binary_instruction :=
  let! o1 := operand_to_bin i.(instr_operande1) in
  fun o1 => ret o1.

Lemma test_proof : forall (i : instruction) (bi : binary_instruction), encode_mytho i = Some bi -> length bi = 32.
Proof.
  intros.
  unfold encode_mytho in H.
  
  

Definition decode (bi : binary_instruction) : option instruction :=
  match get_first_n_bit bi 8 with
  | (li,next) => let! t := lookdown (bit_n li) encdec in
                 fun t => match get_first_n_bit next 8 with
                          | (op1,next) => match get_first_n_bit next 8 with
                                          | (op2,next) => match get_first_n_bit next 8 with
                                                          | (op3,next) => match t with
                                                                          | tag_n tn => Some (mk_instr t
                                                                                                       (bin_to_operand op1)
                                                                                                       (bin_to_operand op2)
                                                                                                       (bin_to_operand op3))
                                                                          | tag_i ti => Some (mk_instr t
                                                                                                       (bin_to_operand op1)
                                                                                                       (bin_to_operand op2)
                                                                                                       (immediate (bit_n op3)))
                                                                          end
                                                          end
                                          end
                          end
  end.


Print my_instr.
Definition my_instr_encoded_decoded := match encode my_instr with
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
    intros i.
    induction i.(instr_opcode).
    -intros bi Hencode.
     unfold encode in Hencode.
     
     apply Hencode in lookdown_encdec'.
  }
Admitted.


Lemma encode_size : forall (i : instruction) (bi : binary_instruction), encode i = Some bi -> length bi = 32.
Proof.
  intros i bi.
  induction i.
  unfold encode.
  destruct (lookup instr_opcode encdec).
  -{
      destruct (n_bit 8 n).
      -{
          destruct (operand_to_bin instr_operande1).
          -{
              destruct (operand_to_bin instr_operande2).
              -{
                  destruct (operand_to_bin instr_operande3).
                  -{
                      admit.
                    }
                  -discriminate.
                }
              -discriminate.
            }
            -discriminate.
        }
        -discriminate.
  }
  -discriminate.
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
  




