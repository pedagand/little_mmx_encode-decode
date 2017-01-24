Open Scope list_scope.
Require Import List.
Import ListNotations.

(* XXX: all of this (and more) is already defined in the Coq stdlib: 
[https://coq.inria.fr/library/Coq.PArith.BinPos.html] 

 To get it, you need to [[Require Import ZArith.]] *)


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

Compute convert_inv 5.

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


(* this function takes a bool list that represent a binary number but it has to be reverse before calling this function *)
Fixpoint binaryInv_to_bin (l : list bool) : bin :=
  match l with
    | [] => zero
    | elem :: suite => if elem
                       then DoubPlsOne (binaryInv_to_bin suite)
                       else Doub (binaryInv_to_bin suite)
  end.
