Require Import List.
 
(* tag definition *)
Inductive arithMode :=
  NORMAL | UNSIGNED | FLOAT.

Inductive tag_ter :=
| ADD : arithMode -> tag_ter
| SUB : arithMode -> tag_ter
| MUL : arithMode -> tag_ter
| DIV : arithMode -> tag_ter
| BIDON : tag_ter.

Inductive tag_duo :=  
| BZ : tag_duo
| BIDON_DUO : tag_duo.

Inductive tag_uno :=
| BIDON_UNO2
| BIDON_UNO.

Inductive tag :=
| tag_t : tag_ter -> tag
| tag_d : tag_duo -> tag                       
| tag_u : tag_uno -> tag.





Scheme Equality for tag.


Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t;
  repeat (destruct t; try destruct a; reflexivity).
Qed.
   
   

  
Lemma tag_beq_different : forall (t1 t2 : tag), tag_beq t1 t2 = true -> t1 = t2.
Proof.
Admitted.
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)

Inductive instructionStructure_t :=
| RRR | RRI | RIR | IRR | RII | III | IRI.

Inductive instructionStructure_d :=
| RR | RI | IR | II.

(* todo je veux que un truc ici mais bon on verra plus tard *)
Inductive instructionStructure_u :=
| I | R.

Inductive instructionStructure :=
| is_t : instructionStructure_t -> instructionStructure
| is_d : instructionStructure_d -> instructionStructure
| is_u : instructionStructure_u -> instructionStructure.


Scheme Equality for instructionStructure.

Lemma instructionStructure_beq_reflexivity : forall (i :instructionStructure), instructionStructure_beq i i = true.
Proof.
  destruct i; destruct i; auto.
Qed.


Lemma instructionStructure_beq_different : forall (i1 i2 : instructionStructure),
    instructionStructure_beq i1 i2 = true -> i1 = i2.
Proof.
  Admitted.


Inductive operande :=
  | imm : nat -> operande
  | reg : nat -> operande.
 

(* instruction definition *)
Record instruction_tern :=
  mk_instr_t { instr_opcode_t : tag_ter;
                 instr_mode_t : instructionStructure_t;
                   instr_operande1_t : operande ; 
                 instr_operande2_t : operande ; 
                 instr_operande3_t : operande }.

Record instruction_duo :=
  mk_instr_d { instr_opcode_d : tag_duo;
               instr_mode_d : instructionStructure_d;
               instr_operande1_d : operande ; 
               instr_operande2_d : operande }.

Record instruction_uno :=
  mk_instr_u { instr_opcode_u : tag_uno;
               instr_mode_u : instructionStructure_u;
               instr_operande1_u : operande}.





Inductive instruction :=
| instr_t : instruction_tern -> instruction
| instr_d : instruction_duo -> instruction
| instr_u : instruction_uno -> instruction.
                                     
(* binary instruction definition *)
Definition binary_instruction := list bool.


(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


