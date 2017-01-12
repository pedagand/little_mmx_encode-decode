Require Export Bool Sumbool.
Require Vector.
Export Vector.VectorNotations.
Require Import Minus.
Require Import Arith.
Require Import Ascii.
Require String.
Open Scope string_scope.
Open Scope list_scope.


(* datatypes for the instructions *)

(* XXX: Use english everywhere *)
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

(* XXX: do not use Vectors (they are broken in Coq). Just use lists of
   boolean, without size indexing *)
Definition Bnil := @Vector.nil bool.

Definition Bcons := @Vector.cons bool.


(* datatypes for the binary instructions *)

(* XXX: binary instructions should just be lists of booleans, no
  need/reason to have more structure than that *)

Inductive opcode : Type :=
| opc : @Vector.t bool 8 -> opcode.

Inductive operande_binary : Type :=
| reg_binary : @Vector.t bool 8 -> operande_binary.

Inductive binary_instruction : Type :=
| binary_instr : opcode -> operande_binary -> operande_binary -> operande_binary -> binary_instruction.



(* fonctions pour manipuler les instructions avec tests *)

Example my_instr := instr ADD (reg (general_reg 10)) (reg (general_reg 11)) (reg (general_reg 10)).

Check my_instr.

(* XXX: if you are to write getters, then probably that you wanted to
   define a [Record] instead *)

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

(* XXX: yes, we won't do parsing for now: we assume that piece of
   software gives us a list of [instruction] *)

(* Idée pour la suite, à l'aide de fichier on crée tout un tas d'éléments de type correspondance
Inductive correspondance_etiquette : Type := 
| binary_to_instruction : binary -> etiquette -> correspondance_etiquette
| instruction_to_binary : etiquette -> binary -> correspondance_etiquette 
     Cela permettrait donc aux fonctions de prendre une liste de ces correspondances qui seraient crée au démarage du
     programme afin que la maintenabilité du programme soit plus aisée (parceque sinon ça serait un gros switch ?)*) 

(* XXX: this is just a pair [opcode * etiquette] *)
Inductive correspondance_etiquette : Type :=
| opcode_to_etiquette : opcode -> etiquette -> correspondance_etiquette.

Inductive correspondance_operande : Type :=
| operande_to_operande_binary : operande -> operande_binary -> correspondance_operande.
\
(* XXX: this is just an association list, of type [list (opcode *
   etiquette)]. But I recommend using [MSet]
   [https://coq.inria.fr/library/Coq.MSets.MSets.html] instead. This
   library is hard to import, let me know if you need help. *)

Inductive correspondance_etiquette_table : Type :=
| correspondance_nil : correspondance_etiquette_table
| correspondance_cons : correspondance_etiquette -> correspondance_etiquette_table -> correspondance_etiquette_table.

Inductive correspondance_operande_table : Type :=
| correspondance_op_nil : correspondance_operande_table
| correspondance_op_cons : correspondance_operande -> correspondance_operande_table -> correspondance_operande_table.


(* TODO :: function which take a decimal value and return the vector of bites corrsponding to it's binary representation *)

Definition create_a_vector := (Bcons true 7
                                     (Bcons true 6
                                            (Bcons true 5
                                                   (Bcons true 4
                                                          (Bcons true 3 (Bcons true 2 (Bcons true 1 (Bcons true 0 Bnil)))))))).

Definition my_instr_binary := binary_instr (opc create_a_vector) (reg_binary create_a_vector) (reg_binary create_a_vector)
                                           (reg_binary create_a_vector).

Definition ADD_correspondance :=  opcode_to_etiquette (opc create_a_vector) ADD.
Definition AND_correspondance :=  opcode_to_etiquette (opc create_a_vector) AND.
Check ADD_correspondance.
Definition correspondance_table := correspondance_cons (ADD_correspondance) correspondance_nil.


(* Fonctions de comparaisons *)

(* XXX: Check [Scheme Equality for ident1] in [https://coq.inria.fr/refman/Reference-Manual015.html] *)

Definition etiquettes_equals (e1 e2 : etiquette) : bool :=
  match (e1,e2) with
  | (ADD,ADD) => true
  | (AND,AND) => true
  | _ => false
  end.


(* Fonctions de décodage *)

(* Premiere fonction afin de décoder une étiquette *)

(* XXX: use the operations (in the standard library) related to [MSet] *)

Fixpoint etiquette_to_binary (t : correspondance_etiquette_table) (etiq : etiquette) : (option opcode) :=
  match t with
  | correspondance_nil => None
  | correspondance_cons elem suite => match elem with
                                     | opcode_to_etiquette o e => if etiquettes_equals etiq e
                                                                 then Some o
                                                                 else etiquette_to_binary suite etiq
                                     end
  end.


Fixpoint instruction_to_binary (t_etiquette : correspondance_etiquette_table)
         (t_opcode : correspondance_operande_table) (i : instruction) : binary_instruction :=
  my_instr_binary.
match etiquette_to_binary t_etiquette (* get_etquette i *) with
| None => None
| Some res => None (* La suite de la fonction *).
end.
(* dans la suite de la fonction il faut matcher les différentes cases et retouner *)

(* XXX: you also need to take a list of instructions and convert them
   to a list of booleans, and conversely from lists of booleans to
   instructions (when possible) *)

(* TODO :: faire une fonction qui convertie les decimaux en string d'éxa (tricks /16) *)


(* XXX: what are the theorems? *)

