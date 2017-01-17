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
(* to use this module you have to compile the binary.v file "coqc binary.v "*)
Require Import binary.


(* datatypes for the instructions *)

(* The boolean use here allow us to know if it is the code with argument z as an immediate or not 
Instructions which have only one representation don't need a bool argument *)
Inductive tag_with_immediate : Type :=
| ADD_I : tag_with_immediate
| AND_I : tag_with_immediate.

Inductive tag_without_immediate : Type :=
| ADD : tag_without_immediate.

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
 binary_instr { opco : opcode ; firstOperande : operande_binary ;secondOperande:operande_binary;firdOperande : operande_binary }.



(* Exemples d'utilisation des structures de données *)

Example my_instr := instr (tag_i ADD_I) (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)).

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

Definition create_a_list := [true;true;true;true;true;true;true;true].
Definition create_a_list_bis := true :: true :: true :: true :: true :: true :: true :: true :: [].


Definition my_instr_binary := binary_instr (opc create_a_list) (op_binary create_a_list) (op_binary create_a_list)
                                           (op_binary create_a_list).

Definition ADD_correspondance :=  opcode_to_tag ((opc create_a_list),(tag_i ADD_I)).
Definition AND_correspondance :=  opcode_to_tag ((opc create_a_list),(tag_i AND_I)).
Check ADD_correspondance.
Definition correspondance_table_example := ADD_correspondance :: AND_correspondance :: [].
Check correspondance_table_example.


(* Fonctions de comparaisons *)

(* XXX: Check [Scheme Equality for ident1] in [https://coq.inria.fr/refman/Reference-Manual015.html] *)

Definition tags_equals (e1 e2 : tag) : bool :=
  match (e1,e2) with
    | (tag_i t1, tag_i t2) => match (t1,t2) with
                                   | (ADD_I,ADD_I) => true
                                   | (AND_I,AND_I) => true
                                   | _ => false
                                 end
    | (tag_no_i t1, tag_no_i t2) => match (t1,t2) with
                                      | (ADD,ADD) => true
                                    end
    | _ => false
  end.

Fixpoint list_bool_equal (l1 l2 : list bool) : bool :=
  match (l1,l2) with 
  | ([],[]) => true
  | ([],_) => false
  | (_,[]) => false
  | ((elem1 :: suite1),(elem2 :: suite2)) => (eqb elem1 elem2) && (list_bool_equal suite1 suite2)  
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
(* Same function as find_tag_list but in the opposite way to find a tag with the correspondance list *)
Fixpoint find_opcode_list (t : list correspondance) (o : opcode) : (option tag) :=
  match (t,o) with
  | ([],_) => None
  | ((elem :: suite),(opc opb)) => match elem with
                     | opcode_to_tag (opc(op),t) => if list_bool_equal opb op 
                                                    then Some t
                                                    else find_opcode_list suite o
                     | operande_to_operande_binary _ => find_opcode_list suite o
                                 end
  end.

(* TODO :: need to do this with things that pierre tolds *)
Fixpoint operande_equals (op1 op2 : operande) : bool :=
  match (op1,op2) with
    | (immediate n1, immediate n2) => beq_nat n1 n2
    | (reg r1, reg r2) => match (r1,r2) with
                                      | (general_reg n1,general_reg n2) => beq_nat n1 n2
                                      | (special_reg r1, special_reg r2) => match (r1,r2) with
                                                                              | (rB,rB) => true
                                                                              | (rD,rD) => true
                                                                              | _ => false
                                                                            end
                                      | _ => false
                                    end
    | (empty,empty) => true
    | _ => false
  end.

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

Fixpoint find_operande_binary_list (t : list correspondance) (op : operande_binary) : (option operande) :=
  match (t,op) with 
  | ([],_) => None
  | ((elem :: suite),(op_binary op_b)) => match elem with 
                     | opcode_to_tag _ => find_operande_binary_list suite op
                     | operande_to_operande_binary (op_binary(op_b2),o) => if list_bool_equal op_b op_b2
                                                                           then Some o
                                                                           else find_operande_binary_list suite op
                                          end
  end.



(* Functions to convert list bool which represent binary numbers to nat *)
Definition binary_to_nat (l : list bool) : nat :=
  convert (binaryInv_to_bin (rev l)).


Definition nat_to_binary (n : nat) : list bool :=
  bin_to_binary (convert_inv n).

Compute binary_to_nat [false].
Compute nat_to_binary 4.





(* Function to convert an immediate operande to it's binary representation *)
(* after make a little function to translate operande *)
(* To translate an operande to it's binary representation Note: We don't need an equivalent function for the tag because 
if the tag isn't in the list then it mean that it have no translation *)
Definition operande_to_binary (t : list correspondance) (op : operande) : option operande_binary :=
  match op with
    | immediate n => Some(op_binary (nat_to_binary n))
    | reg n => find_operande_list t op 
    | empty => None
  end.

(* this function should be call only when you know that the binary_operand is not an immediate *)
(* You can know theese stuff because of the opcode that you get before *) 
Definition binary_operande_to_bool_list (op_b : operande_binary) : nat := 
  match op_b with
    | op_binary l => binary_to_nat l
  end.

(* Record binary_instruction :=
 binary_instr { op : opcode ; firstOperande : operande_binary ;secondOperande:operande_binary;firdOperande : operande_binary }. *)
(* find_tag_list table instruction *)
(* TODO :: il faudrat rajouter du error handling lors d'un retour None de la fonction operande_to_binary *)
Definition instruction_to_binary (table : list correspondance) (i : instruction) : option binary_instruction :=
  match i with
    | instr t op1 op2 op3 => match find_tag_list table t with
                               | None => None
                               | Some tag_convert => let op_b1 := match operande_to_binary table op1 with
                                                       | Some(res) => res | None => op_binary [] end in
                                        let op_b2 := match operande_to_binary table op2 with
                                                       | Some(res) => res | None => op_binary [] end in
                                        let op_b3 := match operande_to_binary table op3 with
                                                       | Some(res) => res | None => op_binary [] end in
                                        Some(binary_instr tag_convert op_b1 op_b2 op_b3)
                             end
  end.

Definition binary_to_instruction (table : list correspondance) (i_b : binary_instruction) : option instruction :=
  match i_b with
    | binary_instr o op_b1 op_b2 op_b3 => let translate_op_b1 := match find_operande_binary_list table op_b1 with
                                                                   | Some res => res | None => empty end in
                                          let translate_op_b2 := match find_operande_binary_list table op_b2 with
                                                                   | Some res => res | None => empty end in
                                          match find_opcode_list table o with
                                            | Some(tag_i res_tag) => Some(instr (tag_i  res_tag) translate_op_b1 translate_op_b2 
                                                                                (immediate (binary_operande_to_bool_list op_b3)))
                                            | Some(tag_no_i res_tag) =>
                                              let translate_op_b3 := match find_operande_binary_list table op_b2 with
                                                                       | Some res => res | None => empty end in
                                              Some(instr (tag_no_i res_tag) translate_op_b1 translate_op_b2 translate_op_b3)
                                            | None => None
                                          end
  end.

(* correspondance_table_example to test the function *)
(* Example my_instr := instr (tag_i ADD_I) (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)). *)
Example my_instr2 := instr (tag_i ADD_I) (immediate 4) (immediate 7) (immediate 8).
Compute instruction_to_binary correspondance_table_example my_instr2.

  
(* Fixpoint binary_to_instruction (table : list correspondance) (i : binary_instruction) : option instruction :=
  match i with 
  | binary_instr opc op1 op2 op3 => let res := *)
  

  
(* dans la suite de la fonction il faut matcher les différentes cases et retouner *)

(* XXX: you also need to take a list of instructions and convert them
   to a list of booleans, and conversely from lists of booleans to
   instructions (when possible) *)



(* XXX: what are the theorems? *)



