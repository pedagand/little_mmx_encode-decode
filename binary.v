Require Import Bool List NArith.
Import ListNotations.

(* functions from positive to list bool and in the opsite way *)
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
Compute list_bool_to_nat my_test_list.