Open Scope list_scope.
Require Import List.
Import ListNotations.
Require Export Bool Sumbool.
Require Import NArith.

(* definition of equality over bool list *)
Scheme Equality for list.
Check list_beq.
Definition list_bool_beq (l1 l2 : list bool) : bool := list_beq bool eqb l1 l2.

(* Some test of th boolean equality *)
Definition lBoolTest1 := true :: true :: false :: false :: [].
Definition lBoolTest2 := true :: true :: false :: false :: [].
Compute list_bool_beq lBoolTest1 lBoolTest2.



(* Fonction to translate a positive to a boolean list *)
Fixpoint positive_to_list_bool (p : positive) : list bool :=
  match p with
    | xI p' => true :: positive_to_list_bool p'
    | xO p' => false :: positive_to_list_bool p'
    | xH => true :: []
  end.

                                        
  
Theorem positive_to_list_bool_not_empty : forall (p : positive),
                                            positive_to_list_bool p = [] -> False.
Proof. intros p. induction p.
       -simpl. discriminate.
       -discriminate.
       -discriminate.
Qed.
                       
Fixpoint list_bool_to_positive (l : list bool) : option positive :=  
  match l with
    | [true] => Some xH
    | x :: l' => match list_bool_to_positive l' with
                   | Some(x') => if x then Some (xI x') else Some (xO x')
                   | None => None
                 end
    | [] => None
  end.

Theorem list_bool_empty_implied_none : forall (l : list bool),
                                         l = [] -> (list_bool_to_positive l = None).
Proof.
  intros l. induction l.
  -simpl. intros h. reflexivity.
  -intros h. rewrite -> h. simpl. reflexivity.
Qed.

(* Lemma list_bool_ *)

(*     IHp : list_bool_to_positive (positive_to_list_bool p) = Some p *)
(*   ============================ *)
(*   list_bool_to_positive *)
(*     match p with *)
(*     | (_~1)%positive => true :: positive_to_list_bool p *)
(*     | (_~0)%positive => true :: positive_to_list_bool p *)
(*     | 1%positive => [true] *)
(*     end = Some (p~1)%positive *)
(* Compute list_bool_to_positive lBoolTest1. *)


Theorem positive_to_list_bool_eq : forall (p : positive),
                                     list_bool_to_positive (positive_to_list_bool p) = Some p.
Proof. intros p. induction p.
       Focus 3. simpl.
        
Theorem list_bool_positive_equal : forall (l : list bool) (p : positive),
                                     list_bool_to_positive l = Some p -> positive_to_list_bool p = l.
Proof. intros l p. intros H. induction p.
       -rewrite <- IHp. simpl. 

         
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

(* old implementation to remove later *)

(* XXX: all of this (and more) is already defined in the Coq stdlib: 
[https://coq.inria.fr/library/Coq.PArith.BinPos.html] 

 To get it, you need to [[Require Import ZArith.]] *)


(* Inductive bin : Type := *)
(*   | zero : bin *)
(*   | Doub : bin -> bin *)
(*   | DoubPlsOne : bin -> bin. *)

(* Fixpoint increment (b : bin) : bin := *)
(*   match b with *)
(*     | zero => DoubPlsOne zero *)
(*     | Doub b' => DoubPlsOne b' *)
(*     | DoubPlsOne b' => Doub (increment b') *)
(*   end. *)

(* Fixpoint convert (b : bin) : nat := *)
(*   match b with *)
(*     | zero => 0 *)
(*     | Doub b' => 2 * convert (b') *)
(*     | DoubPlsOne b' => (2 * convert (b')) + 1 *)
(*   end. *)

(* (* now this is the convertion from a nat to a binary representation *) *)

(* Fixpoint convert_inv (n : nat) : bin := *)
(*   match n with *)
(*     | O => zero *)
(*     | S n' =>  *)
(*       match convert_inv(n') with *)
(*         | zero => DoubPlsOne zero *)
(*         | Doub n'' => DoubPlsOne n'' *)
(*         | DoubPlsOne n'' => Doub (increment n'') *)
(*       end *)
(*   end. *)

(* Compute convert_inv 5. *)

(* Fixpoint add_bool_end_list (l : list bool) (b : bool) : list bool := *)
(*   match l with *)
(*   | nil => [ b ] *)
(*   | cons x l => x :: add_bool_end_list l b *)
(*   end. *)


(* (* I need the begining boolean for this function for the case of the 0 to create a liste [false] *) *)
(* Fixpoint bin_to_binary_aux (b : bin) (begining : bool) : list bool := *)
(*   match b with *)
(*     | zero => if begining then false :: [] else [] *)
(*     | Doub n'' => add_bool_end_list (bin_to_binary_aux n'' false) false *)
(*     | DoubPlsOne n'' => add_bool_end_list (bin_to_binary_aux n'' false) true *)
(*   end. *)

(* Definition bin_to_binary (b : bin) : list bool := *)
(*   bin_to_binary_aux b true. *)


(* (* this function takes a bool list that represent a binary number but it has to be reverse before calling this function *) *)
(* Fixpoint binaryInv_to_bin (l : list bool) : bin := *)
(*   match l with *)
(*     | [] => zero *)
(*     | elem :: suite => if elem *)
(*                        then DoubPlsOne (binaryInv_to_bin suite) *)
(*                        else Doub (binaryInv_to_bin suite) *)
(*   end. *)
