Require Import List.

(* tag definition *)
Inductive tag_ter_normal :=
| ADD : tag_ter_normal
| AND : tag_ter_normal.

Inductive tag_ter_immediate :=
| ADD_I : tag_ter_immediate
| AND_I : tag_ter_immediate.

Inductive tag_duo_immediate :=
| JUMP_I : tag_duo_immediate
| JUMP_IC : tag_duo_immediate.

Inductive tag_duo_normal :=
| JUMP : tag_duo_normal
| JUMPC : tag_duo_normal.


Inductive tag :=
| tag_t_n : tag_ter_normal -> tag
| tag_t_i : tag_ter_immediate -> tag
| tag_d_i : tag_duo_immediate -> tag
| tag_d_n : tag_duo_normal -> tag.

Scheme Equality for tag.


Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t.
  -destruct t.
   +reflexivity.
   +reflexivity.
  -destruct t.
   +reflexivity.
   +reflexivity.
  -destruct t.
   +reflexivity.
   +reflexivity.
  -destruct t.
   +reflexivity.
   +reflexivity. 
Qed.

Lemma tag_beq_different : forall (t1 t2 : tag), tag_beq t1 t2 = true -> t1 = t2.
Proof.
  destruct t1.
  -{
      destruct t2.
      -{
          destruct t.
          -destruct t0.
           +reflexivity.
           +discriminate.
          -destruct t0.
           +discriminate.
           +reflexivity.            
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
    }
  -{
      destruct t2.
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +reflexivity.
           +discriminate.
          -destruct t0.
           +discriminate.
           +reflexivity.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }      
    }
  -{
      destruct t2.
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +reflexivity.
           +discriminate.
          -destruct t0.
           +discriminate.
           +reflexivity.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }      
    }
  -{
      destruct t2.
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +discriminate.
           +discriminate.
          -destruct t0.
           +discriminate.
           +discriminate.
        }
      -{
          destruct t.
          -destruct t0.
           +reflexivity.
           +discriminate.
          -destruct t0.
           +discriminate.
           +reflexivity.
        }
    }
Qed.
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)


Inductive  imediate :=
  imm : nat -> imediate.
Inductive register :=
  reg : nat -> register.

Inductive operande :=
  | imm_o : imediate -> operande
  | reg_o : register -> operande.
 

(* instruction definition *)
Record instruction_tern_n :=
  mk_instr_t_n { instr_opcode_t_n : tag_ter_normal; 
             instr_operande1_t_n : register ; 
             instr_operande2_t_n : register ; 
             instr_operande3_t_n : register }.

Record instruction_tern_i :=
  mk_instr_t_i { instr_opcode_t_i : tag_ter_immediate; 
             instr_operande1_t_i : register ; 
             instr_operande2_t_i : register ; 
             instr_operande3_t_i : imediate }.

Record instruction_duo_n :=
  mk_instr_d_n { instr_opcode_d_n : tag_duo_normal; 
             instr_operande1_d_n : register ; 
             instr_operande2_d_n : register }.

Record instruction_duo_i :=
  mk_instr_d_i { instr_opcode_d_i : tag_duo_immediate; 
             instr_operande1_d_i : register ; 
             instr_operande2_d_i : imediate }.

Inductive instruction :=
| instr_t_n : instruction_tern_n -> instruction
| instr_t_i : instruction_tern_i -> instruction
| instr_d_n : instruction_duo_n -> instruction
| instr_d_i : instruction_duo_i -> instruction.
(* binary instruction definition *)
Definition binary_instruction := list bool.


(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


