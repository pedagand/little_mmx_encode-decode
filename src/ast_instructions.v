Require Import List.

(* tag definition *)
Inductive tag_normal :=
| ADD : tag_normal
| AND : tag_normal.

Inductive tag_immediate :=
| ADD_I : tag_immediate
| AND_I : tag_immediate.


Inductive tag :=
| tag_n : tag_normal -> tag
| tag_i : tag_immediate -> tag.

Scheme Equality for tag.
Check tag_beq.


(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)

(* operand definition *)
Inductive operand :=
| immediate : nat -> operand
| reg : nat -> operand
| empty : operand.


(* instruction definition *)
Record instruction :=
  mk_instr { instr_opcode : tag; 
             instr_operande1 : operand ; 
             instr_operande2 : operand ; 
             instr_operande3 : operand }.

(* binary instruction definition *)
Definition binary_instruction := list bool.


(* some example to test the record structure *)
Example my_instr := mk_instr (tag_i ADD_I) (reg 10) (reg 11) (immediate 12).

Example first_field_instr := my_instr.(instr_opcode).


