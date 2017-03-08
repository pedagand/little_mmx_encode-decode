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
  

Notation "'let!' x ':=' ma 'in' k" := (bind ma k) (at level 30). 

(* TODO :: here i know that i can always get a binary_instruction but some function don't allow me to  *)
(* return a binary_instruction without encapsulate it into an option type *)
Definition encode (i : instruction) : option binary_instruction :=
      let! k := lookup i.(instr_opcode) encdec in
      let! code := n_bit 8 k in
                      | Some code => match operand_to_bin op1 with
                                       | Some o1 => match operand_to_bin op2 with
                                                      | Some o2 => match operand_to_bin op3 with
                                                                     | Some o3 => Some (code ++ o1 ++ o2 ++ o3)
                                                                     | None => None
                                                                   end
                                                      | None => None
                                                    end
                                       | None => None
                                     end
                      | None => None
                    end
        | None => None
      end
  end.

Definition decode (bi : binary_instruction) : option instruction :=
  match lookdown (bit_n (cut_binary_instruction bi 0 8)) encdec with
  | Some t =>
    match t with
    | tag_n tn => Some (mk_instr t (bin_to_operand (cut_binary_instruction bi 7 8))
                                 (bin_to_operand (cut_binary_instruction bi 15 8))
                                 (bin_to_operand (cut_binary_instruction bi 23 8)))
    | tag_i ti => Some (mk_instr t (bin_to_operand (cut_binary_instruction bi 7 8))
                                 (bin_to_operand (cut_binary_instruction bi 15 8))
                                 (immediate (bit_n (cut_binary_instruction bi 23 8))))
    end
  | None => None
  end.

Check instruction.

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
  




