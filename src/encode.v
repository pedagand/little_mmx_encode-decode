Require Import Bool List Arith Nat.
Require Import ast_instructions.
Require Import binary.
Import ListNotations.






(* functions to encode decode instructions *)
(* TODO :: here is that the good reasoning about empty *)
Definition operand_to_bin (o : operand) : option (list bool) :=
  match o with
    | immediate k => n_bit 8 k
    | reg k => n_bit 8 k
    | empty => n_bit 8 0
  end.
                
(* TODO :: here i know that i can always get a binary_instruction but some function don't allow me to 
return a binary_instruction without encapsulate it into an option type *)
Definition encode_bis (i : instruction) : option binary_instruction :=
  match i with
    | mk_instr t op1 op2 op3 =>
      match lookup t encdec with
        | Some k => match n_bit 8 k with
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




                