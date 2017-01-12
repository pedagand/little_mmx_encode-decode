Require Export Bool Sumbool.
Require Vector.
Export Vector.VectorNotations.
Require Import Minus.

Module mmix_en_de_code.

  (* datatypes for the instructions *)
   
  Inductive etiquette : Type :=
| ADD : etiquette
| AND : etiquette.
  
  Inductive operande : Type :=
  | immediate : nat -> operande
  | reg : nat -> operande
  | vide : operande.
  
  Inductive instruction : Type :=
  | instr : etiquette -> operande -> operande -> operande -> instruction.

  (* some definition to make boolean vector manipulation easyer *)
  
  Definition Bnil := @Vector.nil bool.

  Definition Bcons := @Vector.cons bool.
  
  (* datatypes for the binary instructions *)

  
  
  Inductive opcode : Type :=
  | opc : @Vector.t bool 8 -> opcode.

  Inductive operande_binary : Type :=
  | reg_binary : @Vector.t bool 8 -> operande_binary.

  
  Definition my_instr := instr ADD (reg 10) (reg 11) (reg 10).
  
  Check my_instr.

  Definition get_etiquette (i : instruction) : etiquette :=
    match i with
      | instr tag _ _ _ => tag
    end.
  
  Example test_get_etiquette:
    get_etiquette my_instr = ADD. simpl. reflexivity. Qed.

  Definition get_first_operande (i : instruction) : operande :=
    match i with
      | instr _ op _ _ => op
    end.

  Example test_get_first_operande:
    get_first_operande my_instr = reg 10. simpl. reflexivity. Qed.
  
  Definition get_second_operande (i : instruction) : operande :=
    match i with
      | instr _  _ op _ => op
    end.

    Definition get_third_operande (i : instruction) : operande :=
    match i with
      | instr _  _ _ op => op
    end.



    