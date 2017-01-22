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
Require Import MSets.
Require Import MSets.MSetList.
Require Import Coq.FSets.FMapList Coq.Structures.OrderedTypeEx.
(* to use this module you have to compile the binary.v file "coqc binary.v "*)

(* Check mem. *)

(* XXX: use [coq_makefile] with a [_CoqProject] as described here
[https://coq.inria.fr/refman/Reference-Manual017.html#Makefile] *)

(* TODO :: use the already implemented version of this *)
(* Require Import binary. *)


(* datatypes for the instructions *)
(* now i just put a nat here because it's hard to make an association list with something else than a nat now *)
Inductive tag_with_immediate : Type :=
| ADD_I : tag_with_immediate 
| AND_I : tag_with_immediate.

Inductive tag_without_immediate : Type :=
(* XXX: isn't there an [AND] version without immediate? *)
| ADD : tag_without_immediate
| AND : tag_without_immediate.


Inductive tag : Type :=
| tag_i : nat -> tag_with_immediate -> tag
| tag_no_i : nat -> tag_without_immediate -> tag.


(* there is 256 register and 32 special register *)
(* i only give two special register to test but i will not give the exhaustive list (at least for the moment) *)
Inductive special_register : Type :=
| rB : special_register
| rD : special_register.

Inductive register : Type :=
| general_reg : nat -> register
| special_reg : special_register -> register.

Inductive operand : Type :=
| immediate : nat -> operand
| reg : register -> operand
| empty : operand.


Record instruction :=
  (* XXX: [firstField], [secondField], [thirdField] and [fourthField]?? Are you kidding me?*)
  (* ANSWER : it was just for the name or the type representation ? :p *)
  mk_instr { instr_opcode : tag; 
             instr_operande1 : operand ; 
             instr_operande2 : operand ; 
             instr_operande3 : operand }.


(* datatypes for the binary instructions *)

(* XXX: binary instructions should just be lists of booleans, no
  need/reason to have more structure than that *)

Definition binary_instruction := list bool.

(* Some examples to test a little bit the functions *)

Example my_instr := mk_instr (tag_i 10 ADD_I)
                             (reg (general_reg 10))
                             (reg (general_reg 11))
                             (reg (general_reg 10)).

Check my_instr.

Example first_field_instr := my_instr.(instr_opcode).
Check first_field_instr.


(* XXX: this is just an association list, of type [list (tag *
   list bool)]. But I recommend using [MSet]
   [https://coq.inria.fr/library/Coq.MSets.MSets.html] instead. This
   library is hard to import, let me know if you need help. *)

(* TODO :: here i have to define an association list of type (tag * list bool) 
 and i think that i will have to do another one for the registers *)



Definition create_a_list := [true;true;true;true;true;true;true;true].
(* Definition create_a_list_bis := true :: true :: true :: true :: true :: true :: true :: true :: [].


Definition my_instr_binary := binary_instr (create_a_list) (create_a_list) (create_a_list)
                                           (create_a_list).

Definition ADD_correspondance :=  opcode_to_tag ((create_a_list),(tag_i ADD_I)).
Definition AND_correspondance :=  opcode_to_tag ((create_a_list),(tag_i AND_I)).
Check ADD_correspondance.
Definition correspondance_table_example := ADD_correspondance :: AND_correspondance :: [].
Check correspondance_table_example. *)


(* Fonctions de comparaisons *)

(* XXX: Check [Scheme Equality for ident1] in [https://coq.inria.fr/refman/Reference-Manual015.html] *)



Scheme tag_scheme := Induction for tag Sort Set.
Check tag_scheme.

Scheme Equality for tag.

Check tag_with_immediate_beq.
Check tag_without_immediate_beq.
Check tag_beq.
Check tag_eq_dec.

Print tag_beq.

Fixpoint list_bool_beq (l1 l2 : list bool) : bool :=
  match (l1,l2) with 
  | ([],[]) => true
  | ([],_) => false
  | (_,[]) => false
  | ((elem1 :: suite1),(elem2 :: suite2)) => (eqb elem1 elem2) && (list_bool_beq suite1 suite2)  
  end.
(* Fonctions de décodage *)
(* Premiere fonction afin de décoder une étiquette *)
(* XXX: use the operations (in the standard library) related to [MSet] *)

(* XXX: these [find_*] functions are all a big waste of electrons:
there is a single [find] function that lookups up in an association
list / [MSet] which would do the job generically and could then be
instantiated to each individual case.  Fix this code before doing any
proof or you will prove the same facts over and over again. *)

(* To find the opCode of one tag in a correspondance list *)
Scheme Equality for operand.
Print operand_beq.

(* this allow to create some association list from a nat to a boolean list *)
Module Import M := FMapList.Make(Nat_as_OT).

Definition map_nat_bool: Type := M.t (list bool).

Definition find_tag k (m: map_nat_bool) := M.find k m.
Check find_tag.
Definition update_tag (p: nat * (list bool)) (m: map_nat_bool) :=
  M.add (fst p) (snd p) m.

(* function that allow you to decode an opcode to a binaryinstruction *)
Definition opcode_to_binary (t : tag) (m : map_nat_bool) : option(list bool) :=
  match t with
    | tag_i n _ => find_tag n m
    | tag_no_i n _ => find_tag n m
  end.





(* Almot the same as find_tag_list but for the operand *)
Fixpoint find_operand_list (t : list correspondance) (op : operand) : (option operand_binary) :=
  match t with
    | [] => None
    | elem :: suite => match elem with
                         | opcode_to_tag _ => find_operand_list suite op
                         | operand_to_operand_binary (op_b,o) => if operand_equals op o
                                                                   then Some op_b
                                                                   else find_operand_list suite op
                       end
  end.

Fixpoint find_operand_binary_list (t : list correspondance) (op : operand_binary) : (option operand) :=
  match (t,op) with 
  | ([],_) => None
  | ((elem :: suite),( op_b)) => match elem with 
                     | opcode_to_tag _ => find_operand_binary_list suite op
                     | operand_to_operand_binary ((op_b2),o) => if list_bool_equal op_b op_b2
                                                                           then Some o
                                                                           else find_operand_binary_list suite op
                                          end
  end.



(* Functions to convert list bool which represent binary numbers to nat *)

Definition binary_to_nat (l : list bool) : nat :=
  convert (binaryInv_to_bin (rev l)).


Definition nat_to_binary (n : nat) : list bool :=
  bin_to_binary (convert_inv n).

Compute binary_to_nat [false].
Compute nat_to_binary 4.





(* Function to convert an immediate operand to it's binary representation *)
(* after make a little function to translate operand *)
(* To translate an operand to it's binary representation Note: We don't need an equivalent function for the tag because 
if the tag isn't in the list then it mean that it have no translation *)
Definition operand_to_binary (t : list correspondance) (op : operand) : option operand_binary :=
  match op with
    | immediate n => Some((nat_to_binary n))
    | reg n => find_operand_list t op 
    | empty => None
  end.

(* this function should be call only when you know that the binary_operand is not an immediate *)
(* You can know theese stuff because of the opcode that you get before *) 
Definition binary_operand_to_bool_list (op_b : operand_binary) : nat := 
  match op_b with
    | l => binary_to_nat l
  end.

(* Record binary_instruction :=
 binary_instr { op : opcode ; firstOperand : operand_binary ;secondOperand:operand_binary;firdOperand : operand_binary }. *)
(* find_tag_list table instruction *)
(* TODO :: il faudrat rajouter du error handling lors d'un retour None de la fonction operand_to_binary *)
Definition instruction_to_binary (table : list correspondance) (i : instruction) : option binary_instruction :=
  match find_tag_list table i.(firstField) with
  | None => None
  | Some tag_convert => 
    let op_b1 := match operand_to_binary table i.(secondField) with
                 | Some(res) => res 
                 | None => [] end in
    let op_b2 := match operand_to_binary table i.(thirdField) with
                 | Some(res) => res
                 | None => [] end in
    let op_b3 := match operand_to_binary table i.(fourthField) with
                 | Some(res) => res
                 | None =>  [] end in
    Some(binary_instr tag_convert op_b1 op_b2 op_b3)
  end.

Definition binary_to_instruction (table : list correspondance) (i_b : binary_instruction) : option instruction :=
  (* XXX: fix formatting! *)
  match i_b with
    | binary_instr o op_b1 op_b2 op_b3 => let translate_op_b1 := match find_operand_binary_list table op_b1 with
                                                                   | Some res => res | None => empty end in
                                          let translate_op_b2 := match find_operand_binary_list table op_b2 with
                                                                   | Some res => res | None => empty end in
                                          match find_opcode_list table o with
                                            | Some(tag_i res_tag) => Some(mk_instr (tag_i  res_tag) translate_op_b1 translate_op_b2 
                                                                                (immediate (binary_operand_to_bool_list op_b3)))
                                            | Some(tag_no_i res_tag) =>
                                              let translate_op_b3 := match find_operand_binary_list table op_b2 with
                                                                       | Some res => res | None => empty end in
                                              Some(mk_instr (tag_no_i res_tag) translate_op_b1 translate_op_b2 translate_op_b3)
                                            | None => None
                                          end
  end.

(* correspondance_table_example to test the function *)
(* Example my_instr := instr (tag_i ADD_I) (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)). *)
Example my_instr2 := mk_instr (tag_i ADD_I) (immediate 4) (immediate 7) (immediate 8).
Compute instruction_to_binary correspondance_table_example my_instr2.

  
(* Fixpoint binary_to_instruction (table : list correspondance) (i : binary_instruction) : option instruction :=
  match i with 
  | binary_instr opc op1 op2 op3 => let res := *)
  

  
(* dans la suite de la fonction il faut matcher les différentes cases et retouner *)

(* XXX: you also need to take a list of instructions and convert them
   to a list of booleans, and conversely from lists of booleans to
   instructions (when possible) *)



(* XXX: what are the theorems? *)




