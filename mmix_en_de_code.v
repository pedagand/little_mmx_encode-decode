Require Export Bool Sumbool.
Require Vector.
Export Vector.VectorNotations.
Require Import Minus.
Require Import Arith.
Require Import Ascii.
Require String.
Open Scope string_scope.
Open Scope list_scope.
Module mmix_en_de_code.

  (* datatypes for the instructions *)
   
  Inductive etiquette : Type :=
| ADD : etiquette
| AND : etiquette.

  (* there is 256 register and 32 special register *)
  (* i only give two special register to test but i will not give the exhaustive list (at least for the moment) *)
  Inductive special_register : Type :=
  | rB : special_register
  | rD : special_register.
  
  Inductive registre : Type :=
  | general_reg : nat -> registre
  | special_reg : special_register -> registre.
  
  Inductive operande : Type :=
  | immediate : nat -> operande
  | reg : registre -> operande
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




  (* fonctions pour manipuler les instructions avec tests *)
  
  Definition my_instr := instr ADD (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)).
  
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
    get_first_operande my_instr = reg (general_reg 10). simpl. reflexivity. Qed.
  
  Definition get_second_operande (i : instruction) : operande :=
    match i with
      | instr _  _ op _ => op
    end.

    Definition get_third_operande (i : instruction) : operande :=
    match i with
      | instr _  _ _ op => op
    end.

    Definition test_request := "ADD 1 2 3".
    Check test_request.

    (* pour l'instant je ne fais pas encore les fonctions de parsing je fais comme si le parsing m'avais déja remplis mon 
data type *)

    (* Idée pour la suite, à l'aide de fichier on crée tout un tas d'éléments de type correspondance
Inductive correspondance_etiquette : Type := 
| binary_to_instruction : binary -> etiquette -> correspondance_etiquette
| instruction_to_binary : etiquette -> binary -> correspondance_etiquette 
     Cela permettrait donc aux fonctions de prendre une liste de ces correspondances qui seraient crée au démarage du
     programme afin que la maintenabilité du programme soit plus aisée (parceque sinon ça serait un gros switch ?)*) 

    Inductive correspondance_etiquette : Type :=
    | opcode_to_etiquette : opcode -> etiquette -> correspondance_etiquette
    | etiquette_to_opcode : etiquette -> opcode -> correspondance_etiquette.
    
    Inductive correspondance_operande : Type :=
    | operande_to_operande_binary : operande -> operande_binary -> correspondance_operande
    | operande_binary_to_operande : operande_binary -> operande -> correspondance_operande.

    Inductive correspondance_etiquette_table : Type :=
    | correspondance_nil : correspondance_etiquette_table
    | correspondance_cons : etiquette -> correspondance_etiquette -> correspondance_etiquette_table.

    
    