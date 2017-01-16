Require Export Bool Sumbool.
Require Import Minus.
Require Import Arith.
Require Import Notations Logic Datatypes.
Require Import Ascii.
Require String.
Open Scope string_scope.
Open Scope list_scope.
Require Import List.
Import ListNotations.
Require Import Notations Logic Datatypes.
Local Open Scope nat_scope.


(* datatypes for the instructions *)

(* The boolean use here allow us to know if it is the code with argument z as an immediate or not 
Instructions which have only one representation don't need a bool argument *)
Inductive tag_with_immediate : Type :=
| ADD : tag_with_immediate
| AND : tag_with_immediate.

Inductive tag_without_immediate : Type :=
| JUMP : tag_without_immediate.

Inductive tag : Type :=
| tag_i : tag_with_immediate -> tag
| tag_no_i : tag_without_immediate -> tag.
  

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
| empty : operande.


Record instruction :=
  instr { firstField : tag; secondField : operande ; thirdField : operande ; fourthField : operande }.


(* datatypes for the binary instructions *)

(* XXX: binary instructions should just be lists of booleans, no
  need/reason to have more structure than that *)

Inductive opcode : Type :=
| opc : list bool -> opcode.

Inductive operande_binary : Type :=
| op_binary : list bool -> operande_binary.

Record binary_instruction :=
 binary_instr { op : opcode ; firstOperande : operande_binary ;secondOperande:operande_binary;firdOperande : operande_binary }.



(* Exemples d'utilisation des structures de données *)

Example my_instr := instr (tag_i ADD) (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)).

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
| operande_to_operande_binary : (operande_binary * operande) -> correspondance.


(* XXX: this is just an association list, of type [list (opcode *
   tag)]. But I recommend using [MSet]
   [https://coq.inria.fr/library/Coq.MSets.MSets.html] instead. This
   library is hard to import, let me know if you need help. *)

(* TODO :: function which take a decimal value and return the vector of bites corrsponding to it's binary representation *)

Definition create_a_list := [true;true;true;true;true;true;true;true].
Definition create_a_list_bis := true :: true :: true :: true :: true :: true :: true :: true :: [].


Definition my_instr_binary := binary_instr (opc create_a_list) (op_binary create_a_list) (op_binary create_a_list)
                                           (op_binary create_a_list).

Definition ADD_correspondance :=  opcode_to_tag ((opc create_a_list),(tag_i ADD)).
Definition AND_correspondance :=  opcode_to_tag ((opc create_a_list),(tag_i AND)).
Check ADD_correspondance.
Definition correspondance_table_example := ADD_correspondance :: AND_correspondance :: [].
Check correspondance_table_example.


(* Fonctions de comparaisons *)

(* XXX: Check [Scheme Equality for ident1] in [https://coq.inria.fr/refman/Reference-Manual015.html] *)

Definition tags_equals (e1 e2 : tag) : bool :=
  match (e1,e2) with
    | (tag_i t1, tag_i t2) => match (t1,t2) with
                                   | (ADD,ADD) => true
                                   | (AND,AND) => true
                                   | _ => false
                                 end
    | (tag_no_i t1, tag_no_i t2) => match (t1,t2) with
                                      | (JUMP,JUMP) => true
                                    end
    | _ => false
  end.


(* Fonctions de décodage *)
(* Premiere fonction afin de décoder une étiquette *)
(* XXX: use the operations (in the standard library) related to [MSet] *)



(* To find the opCode of one tag in a correspondance list *)

Fixpoint find_tag_list (t : list correspondance) (etiq : tag) : (option opcode) :=
  match t with
    | [] => None
    | elem :: suite => match elem with
                         | opcode_to_tag (op,t) => if tags_equals t etiq
                                                   then Some op
                                                   else find_tag_list suite etiq 
                         | operande_to_operande_binary _ => find_tag_list suite etiq
                       end
  end.

(* TODO :: need to make the real function *)
Fixpoint operande_equals (op1 op2 : operande) : bool :=
  true.

(* Almot the same as find_tag_list but for the operande *)
Fixpoint find_operande_list (t : list correspondance) (op : operande) : (option operande_binary) :=
  match t with
    | [] => None
    | elem :: suite => match elem with
                         | opcode_to_tag _ => find_operande_list suite op
                         | operande_to_operande_binary (op_b,o) => if operande_equals op o
                                                                   then Some op_b
                                                                   else find_operande_list suite op
                       end
  end.


(* This part is needed to compute a list of bool into a natural number*)
Inductive bin : Type :=
  | zero : bin
  | Doub : bin -> bin
  | DoubPlsOne : bin -> bin.

Fixpoint increment (b : bin) : bin :=
  match b with
    | zero => DoubPlsOne zero
    | Doub b' => DoubPlsOne b'
    | DoubPlsOne b' => Doub (increment b')
  end.

Fixpoint convert (b : bin) : nat :=
  match b with
    | zero => 0
    | Doub b' => 2 * convert (b')
    | DoubPlsOne b' => (2 * convert (b')) + 1
  end.

(* now this is the convertion from a nat to a binary representation *)

Fixpoint convert_inv (n : nat) : bin :=
  match n with
    | O => zero
    | S n' => 
      match convert_inv(n') with
        | zero => DoubPlsOne zero
        | Doub n'' => DoubPlsOne n''
        | DoubPlsOne n'' => Doub (increment n'')
      end
  end.

Compute convert_inv 4.

Fixpoint add_bool_end_list (l : list bool) (b : bool) : list bool :=
  match l with
  | nil => [ b ]
  | cons x l => x :: add_bool_end_list l b
  end.


(* I need the begining boolean for this function for the case of the 0 to create a liste [false] *)
Fixpoint bin_to_binary_aux (b : bin) (begining : bool) : list bool :=
  match b with
    | zero => if begining then false :: [] else []
    | Doub n'' => add_bool_end_list (bin_to_binary_aux n'' false) false
    | DoubPlsOne n'' => add_bool_end_list (bin_to_binary_aux n'' false) true
  end.

Definition bin_to_binary (b : bin) : list bool :=
  bin_to_binary_aux b true.


Definition test_binary := convert_inv 4.
Compute test_binary.
Compute bin_to_binary (test_binary).
Compute length create_a_list.

(* this function takes a bool list that represent a binary number but it has to be reverse before calling this function *)
Fixpoint binaryInv_to_bin (l : list bool) : bin :=
  match l with
    | [] => zero
    | elem :: suite => if elem
                       then DoubPlsOne (binaryInv_to_bin suite)
                       else Doub (binaryInv_to_bin suite)
  end.


Definition binary_to_nat (l : list bool) : nat :=
  convert (binaryInv_to_bin (rev l)).


Definition nat_to_binary (n : nat) : list bool :=
  bin_to_binary (convert_inv n).

Compute binary_to_nat [false].
Compute nat_to_binary 4.

(* trying to proove the reversibility of theese functions *)
Theorem conv_nat_binary_nat : forall n : nat,
                                binary_to_nat (nat_to_binary n) = n.
Proof.
  intros n. Abort.




(* Function to convert an immediate operande to it's binary representation *)
(* after make a little function to translate operande *)
(* To translate an operande to it's binary representation Note: We don't need an equivalent function for the tag because 
if the tag isn't in the list then it mean that it have no translation *)
Fixpoint operande_to_binary (t : list correspondance) (op : operande) : (option operande_binary) :=
  match op with
    | immediate n => Some (op_binary (nat_to_binary n))
    | reg n => None (* ici il va falloir faire avec la table de correspondance TODO :: reflechir si ça vaut vraiment la peine *)
    | empty => None 
  end.

(* Record binary_instruction :=
 binary_instr { op : opcode ; firstOperande : operande_binary ;secondOperande:operande_binary;firdOperande : operande_binary }. *)
(* find_tag_list table instruction *)
Fixpoint instruction_to_binary (table : list correspondance) (i : instruction) : option binary_instruction :=
  match i with
    | instr t op1 op2 op3 => let res := find_tag_list table t in                             
                             match res with
                               | Some t => binary_instr { res ;(operande_to_binary op1);(operande_to_binary op2)
                                                          ;(operande_to_binary op3) }
                               | None => None
                             end
  end.
  
  

  
(* dans la suite de la fonction il faut matcher les différentes cases et retouner *)

(* XXX: you also need to take a list of instructions and convert them
   to a list of booleans, and conversely from lists of booleans to
   instructions (when possible) *)

(* TODO :: faire une fonction qui convertie les decimaux en string d'éxa (tricks /16) *)


(* XXX: what are the theorems? *)



