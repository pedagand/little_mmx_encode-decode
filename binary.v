Require Import Bool List Arith Nat.
Import ListNotations.


Fixpoint bit_n_rec (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => (if a then 1 else 0) + (2 * bit_n_rec tl)
  end.

Definition bit_n (l : list bool) : nat :=
  bit_n_rec (rev l).

Definition testing_liste := [true;true;false].
Compute bit_n testing_liste.

(* this function take n as the length of the outside vector (it can fail if the lenght given is not enought to store the 
boolean *)
Search "beq".
Compute ltb 0 0.
Check beq_nat.
Compute div 4 2.
Fixpoint n_bit (n : nat) (k : nat) : option (list bool) :=
  match n with
    | 0 => if ltb k 1 then Some [] else None
    | S n' => match n_bit n' (div k 2) with
                | None => None
                | Some l => Some ((beq_nat (modulo k n) 1) :: l)
              end
  end.

Compute n_bit 30 3.
  

(* old version (* functions from positive to list bool and in the opsite way *)
Fixpoint pos_to_list_acc (p: positive)(acc: list bool): list bool :=
  match p with
  | xH => true :: acc
  | xO p => pos_to_list_acc p (false :: acc)
  | xI p => pos_to_list_acc p (true :: acc)
  end.

Definition pos_to_list (p: positive): list bool := pos_to_list_acc p [].

Fixpoint list_to_pos_acc (l: list bool)(acc: positive): positive :=
  match l with
  | [] => acc
  | true :: l => list_to_pos_acc l (xI acc)
  | false :: l => list_to_pos_acc l (xO acc)
  end.

Definition list_to_pos (l : list bool) : positive := list_to_pos_acc l xH.


(* functions to convert list bool to N and in the opposite way *)
Fixpoint list_bool_to_N (l: list bool): N :=
  match l with
  | [] => N0
  | true :: l => Npos (list_to_pos l)
  | false :: l => list_bool_to_N l
  end.

Definition N_to_list_bool (n: N): list bool :=
  match n with
  | N0 => []
  | Npos p => pos_to_list p
  end.


(* The functions that you should be using outside of this module which are nat to list bool and opposite way *)
Definition nat_to_list_bool (n : nat) : list bool :=
  N_to_list_bool (N_of_nat n).

Definition list_bool_to_nat (l : list bool) : nat :=
   nat_of_N (list_bool_to_N l).


(* TODO :: obviously i will need to make some proof about that *)




(* some test about the functions *)
Set Printing All.
Compute (5)%positive.
Unset Printing All.
Compute (pos_to_list 5).
Compute nat_to_list_bool 4.
Definition my_test_list := true :: false :: true :: false :: [].
Compute list_bool_to_nat my_test_list. *)