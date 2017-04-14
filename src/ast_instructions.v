Require Import List.
 
(* tag definition *)
Inductive arithMode :=
  SIGNED | UNSIGNED | FLOAT.

Inductive opcode :=
| ADD : arithMode -> opcode
| SUB : arithMode -> opcode
| MUL : arithMode -> opcode
| DIV : arithMode -> opcode
| BZ : opcode
(* XXX: Why do you need this? *)
| BIDON : opcode.

Scheme Equality for opcode.

(*
Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t;
  repeat (destruct t; try destruct a; reflexivity).
Qed.
   
   

  
Lemma tag_beq_different : forall (t1 t2 : tag), tag_beq t1 t2 = true -> t1 = t2.
Proof.
Admitted.
  *)  

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)

Inductive operand :=
| imm : operand
| reg : operand.

Inductive operands :=
| unary : operand -> operands
| binary : operand -> operand -> operands
| ternary : operand -> operand -> operand -> operands.

Scheme Equality for operand.
Scheme Equality for operands.

(*
Lemma instructionStructure_beq_reflexivity : forall (i :instructionStructure), instructionStructure_beq i i = true.
Proof.
  destruct i; destruct i; auto.
Qed.


Lemma instructionStructure_beq_different : forall (i1 i2 : instructionStructure),
    instructionStructure_beq i1 i2 = true -> i1 = i2.
Proof.
  Admitted.
*)

(* instruction definition *)


Record instr := mk_instr { instr_opcode : opcode;
                           instr_operand : operands }.
                                     
(* binary instruction definition *)
Definition binary_instruction := list bool.


(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


