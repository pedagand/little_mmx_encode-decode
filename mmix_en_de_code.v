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
Require Import NArith.

(* XXX: use [coq_makefile] with a [_CoqProject] as described here
[https://coq.inria.fr/refman/Reference-Manual017.html#Makefile] *)


(* datatypes for the instructions *)
(* now i just put a nat here because it's hard to make an association list with something else than a nat now *)

(* XXX: this is a *TERRIBLE* idea! Either your slap an order on
[tag_with_immediate] and define the FMap over [tag_with_immediate], or
you implement a function of type [tag_with_immediate -> nat] and
convert the [tag_with_immediate] to [nat] before looking up an FMap
over nat. But you don't duplicate the encoding with a
[tag_with_immediate] *and* a [nat] in the description of the
instruction set! *)

Inductive tag_with_immediate : Type :=
| ADD_I : tag_with_immediate 
| AND_I : tag_with_immediate.

Inductive tag_without_immediate : Type :=
| ADD : tag_without_immediate
| AND : tag_without_immediate.


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

Inductive operand : Type :=
| immediate : nat -> operand
| reg : register -> operand
| empty : operand.


Record instruction :=
  mk_instr { instr_opcode : tag; 
             instr_operande1 : operand ; 
             instr_operande2 : operand ; 
             instr_operande3 : operand }.


(* datatypes for the binary instructions *)

Definition binary_instruction := list bool.

(* Some examples to test a little bit the functions *)

Example my_instr := mk_instr (tag_i ADD_I)
                             (reg (general_reg 10))
                             (reg (general_reg 11))
                             (reg (general_reg 10)).

Check my_instr.

Example first_field_instr := my_instr.(instr_opcode).
Check first_field_instr.



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


Scheme tag_scheme := Induction for tag Sort Set.
Check tag_scheme.

Scheme Equality for tag.

Check tag_with_immediate_beq.
Check tag_without_immediate_beq.
Check tag_beq.
Check tag_eq_dec.

Print tag_beq.

(* XXX: you should obtain [list_bool_beq] from [list_eq_dec]
([https://coq.inria.fr/library/Coq.Lists.List.html#list_eq_dec]) *)
(* Fixpoint list_bool_beq (l1 l2 : list bool) : bool :=
  match (l1,l2) with 
  | ([],[]) => true
  | ([],_) => false
  | (_,[]) => false
  | ((elem1 :: suite1),(elem2 :: suite2)) => (eqb elem1 elem2) && (list_bool_beq suite1 suite2)  
  end. *)
Scheme Equality for list.
Check list_beq.
Definition list_bool_beq (l1 l2 : list bool) : bool := list_beq bool eqb l1 l2.

Definition lBoolTest1 := true :: true :: false :: false :: [].
Definition lBoolTest2 := true :: true :: false :: false :: [].

Compute list_bool_beq lBoolTest1 lBoolTest2.
          
(* Fonctions de décodage *)
(* Premiere fonction afin de décoder une étiquette *)



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

(* REMARK :: ugly function but use for now because i don't wan't to waste so many time to define tag as an ordered type *)
Definition tag_to_nat (t : tag) : nat :=
  match t with
    | tag_i t' => match t' with
                    | ADD_I => 34
                    | AND_I => 33
                  end
    | tag_no_i t' => match t' with
                       | AND => 35
                       | ADD => 36
                     end
  end.
Definition nat_to_tag (n : nat) : option tag :=
  match n with
    | 33 => Some(tag_i AND_I)
    | 34 => Some(tag_i ADD_I)
    | 35 => Some(tag_no_i AND)
    | 36 => Some(tag_no_i ADD)
    | _ => None
  end.

Theorem nat_to_tag_equal : forall (n : nat) (x : tag),
                             nat_to_tag n = Some x -> tag_to_nat x = n.
Proof. Admitted.
(* function that allow you to decode an opcode to a binaryinstruction *)                    
Definition opcode_to_binary (t : tag) (m : map_nat_bool) : option(list bool) :=
  find_tag (tag_to_nat t) m.


(* DELETE :: some tests to know more about boulean with NArith. *)
Check N.of_nat 10.

(* Example bin *)
Fixpoint positive_to_list_bool (p : positive) : list bool :=
  match p with
    | xI p' => true :: positive_to_list_bool p'
    | xO p' => false :: positive_to_list_bool p'
    | xH => true :: []
  end.
Fixpoint list_bool_to_positive (l : list bool) : option positive :=
  match l with
    | [true] => Some xH
    | x :: l' => match list_bool_to_positive l' with
                   | Some(x') => if x then Some (xI x') else Some (xO x')
                   | None => None
                 end
    | _ => None
  end.

                  
Theorem list_bool_positive_equal : forall (l : list bool) (p : positive),
                                     list_bool_to_positive l = Some p -> positive_to_list_bool p = l.
Proof. intros l p. compute.

Theorem positive_list_bool_equal : forall (p : positive),
                                     list_bool_to_positive (positive_to_list_bool p) = Some p.
Proof.
  Admitted.
Definition binary_to_list_bool (b : N) : list bool :=
  match b with
    | N0 => []
    | Npos p => rev (positive_to_list_bool p)
  end.

           
Definition list_bool_to_binary (l : list bool) : N :=
  match l with
    | [] => N0
    | x :: l' => match list_bool_to_positive l with
                   | Some x' => Npos x'
                   | None => N0
                 end
  end.

Definition binary_to_nat (l : list bool) : nat :=
  N.to_nat (list_bool_to_binary (rev l)).

Definition nat_to_binary (n : nat) : list bool :=
  binary_to_list_bool (N.of_nat n).

Definition binary_list_test := [true ; false ; true].
Compute nat_to_binary 6.
Compute binary_to_nat binary_list_test.

(* binary_to_nat *)
Lemma binary_to_nat_destruct : forall l,
                                 N.to_nat (list_bool_to_binary (rev l)) = binary_to_nat l.
Proof.
  intros l. reflexivity. Qed.


  
    Theorem binary_nat_equiv : forall (l : list bool),
                             nat_to_binary (binary_to_nat l) = l.
Proof. Admitted.



  
Theorem nat_binary_equiv : forall (x : nat),
                             binary_to_nat (nat_to_binary x) = x.
Proof.
  Admitted.


     
(* Functions to convert list bool which represent binary numbers to nat *)
(* REMEMBER :: compute is the key word to calculate a value *)






Compute binary_to_nat [false].
Compute nat_to_binary 4.



(* These are function that are not very relevant but for this it's ok *)
Definition special_reg_to_nat (sp : special_register) : nat :=
  match sp with
    | rB => 1
    | rD => 2
  end.
Definition nat_to_special_reg (n : nat) : option special_register :=
  match n with
    | 1 => Some rB
    | 2 => Some rD
    | _ => None
  end.
(* REMARK :: i don't need an association table for binary anymore *)
Definition operand_to_binary (op : operand) : list bool :=
  match op with
    | immediate n => nat_to_binary n
    | reg r =>  match r with
                  | general_reg n => nat_to_binary n
                  | special_reg sp => nat_to_binary (special_reg_to_nat sp)
                end
    | empty => []
  end.
Definition binary_to_register (l : list bool) : option register :=
  let n := binary_to_nat l in
  match nat_to_special_reg n with
    | Some x => Some (special_reg x)
    | None => Some (general_reg n)
  end.
Definition binary_to_operand (l : list bool) (is_immediate : bool) : option operand :=
  if is_immediate
  then Some(immediate (binary_to_nat l))
  else match binary_to_register l with
         | Some x => Some(reg x)
         | None => None
       end.

(* this function should be call only when you know that the binary_operand is not an immediate *)
(* You can know theese stuff because of the opcode that you get before *) 

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




