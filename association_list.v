Require Import List.
Import ListNotations.
Require Import MSets.
Require Import MSetList.

(* you need to have the two list of the same length ect...*)


Print OrderedTypeWithLeibniz.

(* Module OWL. *)
(*   Definition t := nat. *)
(*   Definition eq := @eq t. *)
(*   Instance eq_equiv : Equivalence eq. *)
(*   Definition lt := lt. *)
(*   Instance lt_strorder : StrictOrder lt. *)
(*   Instance lt_compat : Proper (eq ==> eq ==> iff) lt. *)
(*   Proof. *)
(*     now unfold eq; split; subst. *)
(*   Qed. *)
(*   SearchPattern (nat -> nat -> comparison). *)
(*   Definition compare := Compare_dec.nat_compare. *)
(*   SearchAbout CompSpec. *)
(*   (*So, nothing here on nat*) *)
(*   Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y). *)
(*   Proof. *)
(*     SearchPattern (forall x y, Compare_dec.nat_compare x y = _ -> _). *)
(*     intros; case_eq (compare x y); constructor. *)
(*     now apply Compare_dec.nat_compare_eq. *)
(*     now apply Compare_dec.nat_compare_Lt_lt. *)
(*     now apply Compare_dec.nat_compare_Gt_gt. *)
(*   Qed. *)
(*   SearchPattern (forall (a b:nat), {a=b}+{a<>b}). *)
(*   Definition eq_dec := Peano_dec.eq_nat_dec. *)
(*   Definition eq_leibniz a b (H:eq a b) := H. *)
(* End OWL. *)

(* Module NatSet := MakeWithLeibniz OWL. *)

(* Inductive exemple := *)
(* | A : exemple *)
(* | B : NatSet.t -> exemple *)
(* | C : NatSet.t -> bool -> exemple. *)

(* Definition eq_dec : forall (a b:exemple), {a=b}+{a<>b}. *)
(*   intros; decide equality. *)
(*   destruct (NatSet.eq_dec t t0). *)
(*   now left; apply NatSet.eq_leibniz. *)
(*   right; intro; apply n; clear n; subst. *)
(*   reflexivity. *)
(*   apply bool_dec. *)
(*   destruct (NatSet.eq_dec t t0). *)
(*   now left; apply NatSet.eq_leibniz. *)
(*   right; intro; apply n; clear n; subst. *)
(*   reflexivity. *)
(* Defined. *)


Definition assocList (A B : Type) := list (A * B).

Inductive listb := nilb : listb | consb: bool -> listb -> listb.
Scheme Equality for listb.
Print listb_beq.
Fixpoint combine {A B} (l1 : list A) (l2 : list B) : option (assocList A B) :=
  match (l1,l2) with
    | ([],[]) => Some []
    | ((elem :: suite),(elem2 :: suite2)) => match combine suite suite2 with
                                            | Some(l) => Some((elem,elem2) :: l)
                                            | None => None
                                          end
    | _ => None
  end.



Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(Nat_as_OT).

Definition map_nat_nat: Type := M.t nat.
Check map_nat_nat.
Definition find k (m: map_nat_nat) := M.find k m.
Check M.add.
Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.





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
 
Scheme Equality for tag.
Print tag_beq.
Module M' := FMapAVL.Make(Nat_as_OT).
Print FMapAVL.Make.
Definition map_tag_list_bool: Type := M.t tag.

Definition findT k (m: map_nat_nat) := M.find k m.
Check findT.

Require Import Coq.FSets.FMapList Coq.Structures.OrderedTypeEx.

Module Import M'' := FMapList.Make(Nat_as_OT).

Definition map_nat_bool: Type := M''.t (list bool).

Definition find_tag k (m: map_nat_bool) := M''.find k m.
Check find_tag.
Definition update_tag (p: nat * (list bool)) (m: map_nat_bool) :=
  M''.add (fst p) (snd p) m.

(*Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ). *)
Definition listBoolTest := true :: false :: true :: [].
Definition testMap := update_tag (pair 10 listBoolTest) (update_tag (pair 5 listBoolTest) (M''.empty (list bool))).
Example find_test : find 10 testMap = Some(listBoolTest).
Proof. reflexivity. Qed.
Example find_test2 : find 9 testMap = None.
Proof. reflexivity. Qed.

