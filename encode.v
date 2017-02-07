Require Import ast_instructions binary Bool.
Require Import Coq.FSets.FMapList Coq.Structures.OrderedTypeEx.

(* generate equality function for tag *)
Scheme Equality for tag.
Check tag_beq.
Check tag_eq_dec.


(* generate equality function for binary_instruction (over list bool) *)
Scheme Equality for list.
Check list_beq.
Check list_eq_dec.

Definition binary_instruction_eq (l1 l2 : list bool) := list_beq bool eqb l1 l2.

(* function to assiociate each tag with a natural number (i nned this because i don't really understand yet how to define an ordered type *)
Definition tag_to_nat (t : tag) : nat :=
  match t with
    | tag_i t' => match t' with
                    | ADD_I => 34
                    | AND_I => 33
                  end
    | tag_n t' => match t' with
                       | AND => 35
                       | ADD => 36
                  end
    | unknow => 0
  end.
Definition nat_to_tag (n : nat) : tag :=
  match n with
    | 33 => tag_i AND_I
    | 34 => tag_i ADD_I
    | 35 => tag_n AND
    | 36 => tag_n ADD
    | _ => unknow
  end.
(* LEMMA about nat_to_tag and tag_to_nat *)
Lemma tag_to_nat_equiv : forall (n : nat) (x : tag),
                           match (nat_to_tag n) with
                               Some x => (tag_to_nat x = n).


(* create association map to link nat to list bool *)
Module Import M := FMapList.Make(Nat_as_OT).

Definition map_nat_bool: Type := M.t (list bool).
Definition find_tag k (m: map_nat_bool) := M.find k m.

Definition update_tag (p: nat * (list bool)) (m: map_nat_bool) :=
  M.add (fst p) (snd p) m.




(* this theorem seem's to be useless *)
(* Theorem some_equal : forall x : nat, forall y : nat,
                       x = y -> Some x = Some y.
Proof. intros x y H. rewrite H. reflexivity.
Qed. *) 

(* these are the functions to use for the association map betwen tag and boolean list *)
Definition tag_to_binary (t : tag) (m : map_nat_bool) : option(list bool) :=
  find_tag (tag_to_nat t) m.

Definition binary_to_tag (l : list bool) : option tag :=
  nat_to_tag(binary_to_nat l).


Print tag.
(* these are the functions to encode your instruction *)
Definition tag_to_list_bool (t : tag) : list bool :=
  match t with
    | 
 











