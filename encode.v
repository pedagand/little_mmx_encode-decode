Require Import Bool List Arith Nat.
Require Import ast_instructions.
Require Import binary.
Import ListNotations.

Check (1,2).
Check pair nat nat.
Definition tag_opcode_assoc :=
  list (tag * (list bool)).

Scheme Equality for list.
Check list_beq.

Fixpoint get_opcode (t : tag) (l : tag_opcode_assoc) : option (list bool) :=
  match l with
    | [] => None
    | (t',r) :: tl => if tag_beq t t'
                      then Some r
                      else get_opcode t tl
  end.

Fixpoint get_tag (o : list bool) (l : tag_opcode_assoc) : option tag :=
  match l with
    | [] => None
    | (t,o') :: tl => if list_beq bool Bool.eqb o o'
                      then Some t
                      else get_tag o tl
  end.





    
