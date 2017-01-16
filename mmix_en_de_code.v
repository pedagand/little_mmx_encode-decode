Require Export Bool Sumbool.
Require Import Minus.
Require Import Arith.
Require Import Ascii.
Require String.
Open Scope string_scope.
Open Scope list_scope.
Require Import List.
Import ListNotations.


(* datatypes for the instructions *)

(* XXX: Use english everywhere *)
Inductive tag : Type :=
| ADD : tag
| AND : tag.

(* there is 256 register and 32 special register *)
(* i only give two special register to test but i will not give the exhaustive list (at least for the moment) *)
Inductive special_register : Type :=
| rB : special_register
| rD : special_register.

Inductive register : Type :=
| general_reg : nat -> register
| special_reg : special_register -> register.

Inductive operande : Type :=
| immediate : nat -> operande
| reg : register -> operande
| vide : operande.


Record instruction :=
  instr { firstField : tag; secondField : operande ; thirdField : operande ; fourthField : operande }.




(* datatypes for the binary instructions *)

(* XXX: binary instructions should just be lists of booleans, no
  need/reason to have more structure than that *)

Inductive opcode : Type :=
| opc : list bool -> opcode.

Inductive operande_binary : Type :=
| reg_binary : list bool -> operande_binary.

Inductive binary_instruction : Type :=
| binary_instr : opcode -> operande_binary -> operande_binary -> operande_binary -> binary_instruction.



(* Exemples d'utilisation des structures de données *)

Example my_instr := instr ADD (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)).

Check my_instr.

Example first_field_instr := my_instr.(firstField).
Check first_field_instr.

(* pour l'instant je ne fais pas encore les fonctions de parsing je fais comme si le parsing m'avais déja remplis mon 
data type *)

(* XXX: yes, we won't do parsing for now: we assume that piece of
   software gives us a list of [instruction] *)

(* Idée pour la suite, à l'aide de fichier on crée tout un tas d'éléments de type correspondance
Inductive correspondance_tag : Type := 
| binary_to_instruction : binary -> tag -> correspondance_tag
| instruction_to_binary : tag -> binary -> correspondance_tag 
     Cela permettrait donc aux fonctions de prendre une liste de ces correspondances qui seraient crée au démarage du
     programme afin que la maintenabilité du programme soit plus aisée (parceque sinon ça serait un gros switch ?)*) 

(* XXX: this is just a pair [opcode * tag] *)
Inductive correspondance : Type :=
| opcode_to_tag : (opcode*tag) -> correspondance
| operande_to_operande_binary : (operande * operande_binary) -> correspondance.


(* XXX: this is just an association list, of type [list (opcode *
   tag)]. But I recommend using [MSet]
   [https://coq.inria.fr/library/Coq.MSets.MSets.html] instead. This
   library is hard to import, let me know if you need help. *)

Inductive correspondance_table : Type :=
| c_table : list correspondance -> correspondance_table.

(* TODO :: function which take a decimal value and return the vector of bites corrsponding to it's binary representation *)

Definition create_a_list := [true;true;true;true;true;true;true;true].
Definition create_a_list_bis := true :: true :: true :: true :: true :: true :: true :: true :: [].


Definition my_instr_binary := binary_instr (opc create_a_list) (reg_binary create_a_list) (reg_binary create_a_list)
                                           (reg_binary create_a_list).

Definition ADD_correspondance :=  opcode_to_tag ((opc create_a_list),ADD).
Definition AND_correspondance :=  opcode_to_tag ((opc create_a_list),AND).
Check ADD_correspondance.
Definition correspondance_table_example := c_table (ADD_correspondance :: AND_correspondance :: []).


(* Fonctions de comparaisons *)

(* XXX: Check [Scheme Equality for ident1] in [https://coq.inria.fr/refman/Reference-Manual015.html] *)

Definition tags_equals (e1 e2 : tag) : bool :=
  match (e1,e2) with
  | (ADD,ADD) => true
  | (AND,AND) => true
  | _ => false
  end.


(* Fonctions de décodage *)
(* Premiere fonction afin de décoder une étiquette *)
(* XXX: use the operations (in the standard library) related to [MSet] *)


(* TODO :: need to change eveything and i need to try to make some little function to manipulate theese structures *)
Fixpoint tag_to_binary (t : correspondance_table) (etiq : tag) : (option opcode) :=
  match t with
    | c_table elem => match elem with
                                     | opcode_to_tag o e => if tags_equals etiq e
                                                                 then Some o
                                                                 else tag_to_binary suite etiq
                                     end
  end.


Fixpoint instruction_to_binary (t_tag : correspondance_tag_table)
         (t_opcode : correspondance_operande_table) (i : instruction) : binary_instruction :=
  my_instr_binary.
match tag_to_binary t_tag (* get_etquette i *) with
| None => None
| Some res => None (* La suite de la fonction *).
end.
(* dans la suite de la fonction il faut matcher les différentes cases et retouner *)

(* XXX: you also need to take a list of instructions and convert them
   to a list of booleans, and conversely from lists of booleans to
   instructions (when possible) *)

(* TODO :: faire une fonction qui convertie les decimaux en string d'éxa (tricks /16) *)


(* XXX: what are the theorems? *)



