Require Import Bool List Arith Nat.
Import ListNotations.


Fixpoint bit_n_rec (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => (if a then 1 else 0) + (2 * bit_n_rec tl)
  end.

Definition bit_n (l : list bool) : nat :=
  bit_n_rec (rev l).

Definition testing_liste := [false;false;true;false].
Compute bit_n testing_liste.

(* this function take n as the length of the outside vector (it can fail if the lenght given is not enought to store the 
boolean *)
Search "beq".
Compute ltb 0 0.
Check beq_nat.
Compute div 4 2.
Check beq_nat.
Fixpoint n_bit_rec (n : nat) (k : nat) : option (list bool) :=
  if beq_nat k 0 then Some []
  else 
    match n with
      | 0 => if ltb k 1 then Some [] else None
      | S n' => match n_bit_rec n' (div k 2) with
                  | None => None
                  | Some l => Some ((beq_nat (modulo k 2) 1) :: l)
                end
    end.


Definition n_bit (n : nat) (k : nat) : option (list bool) :=
  match n_bit_rec n k with
    | None => None
    | Some x => Some(List.rev x)
  end.

Compute n_bit 10 7.
Compute bit_n [].


Check 2 >= 3.
Compute 3 <= 2.

Theorem bit_n_bit : forall (l : list bool) (n : nat),
                      n >= length l -> (n_bit n (bit_n l)) = Some l.
Proof. Admitted.
  
Theorem n_bit_n : forall (l : list bool) (n k : nat),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (l : list bool) (n k : nat), n_bit n k = Some l -> bit_n l = k).
  {
    intros l n k.
    induction l.
    assert (I_1 : n_bit n k = Some [] -> bit_n [] = k).
     {
       induction k.
       -intros. compute. reflexivity.
       -assert (I_1_1 : n_bit n (S k) = Some [] -> False).
        {          
          destruct (n_bit n (S k)).
          -admit.
          -discriminate.
        }
        intros H.
        compute.
        assert (I_1_2 : ((bit_n [] = S k) -> False)).
        {
          compute.
          apply Nat.neq_0_succ.
        }
        apply False_ind.
        apply I_1_1.
        rewrite H.
        reflexivity.        
     }
    -exact I_1.
    -assert (I_2 : n_bit n k = Some (a :: l) -> bit_n (a :: l) = k).
     {
       destruct a.
       assert(I_2_1 : n_bit n k = Some (true :: l) -> bit_n (true :: l) = k).
       {
         assert (I_2_1_1 : bit_n (true :: l) = k -> bit_n l = 
       }
         
       
     }
    exact I_2.
  }
  exact I.
  (* intros l.  *)
  (* induction l. *)
  (* { *)
  (*   assert (i0 : forall (n k : nat), n_bit n k = Some [] -> bit_n [] = k). *)
  (*   { *)
  (*     destruct k. *)
  (*     -reflexivity. *)
  (*     -assert (j0 : n_bit n (S k) = Some [] -> bit_n [] = S k). *)
  (*      { *)
  (*        induction k. *)
  (*        -intros H. *)
  (*         induction n. *)
  (*         +compute in H. discriminate. *)
  (*         +rewrite <- H in IHn. *)
  (*          apply IHn. *)
  (*          assert(l0 : n_bit n 1 <> n_bit (S n) 1). *)
  (*          { *)
  (*            induction n. *)
  (*            -compute. intros. discriminate. *)
  (*            -rewrite H.  *)
  (*          } *)
           

  (*      } *)
  (*   }     *)
    


      
   (*  assert (k1 : n_bit n 0 = Some [] -> bit_n [] = 0). *)
  (*   { *)
  (*     intros H. *)
  (*     compute. reflexivity. *)
  (*   } *)
  (*   exact k1. *)
  (*   assert (k2 : bit_n [] = k). *)
  (*   { *)
  (*     compute. Search (_=_). *)
  (*     apply eq_sym. *)
  (*     rewrite k0. reflexivity. *)
      
      
  (*   } *)
      
  (* } *)



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





  (* test that can bu usefull *)
  
Lemma some_stuff_eq : forall (t : Type), forall (x y : t),
                        x = y -> Some x = Some y.
Proof.
  intros t x y H.
  rewrite H.
  reflexivity.
Qed.
Lemma some_stuff_eq_other : forall (t : Type), forall (x y : t),
                              Some x = Some y -> x = y.
Proof. Admitted.
Example test_n_bit1 : forall (x : list bool), n_bit 6 10 = Some x -> bit_n x = 10.
Proof.
  intros x.
  intros H.
  compute in H.
  assert(x =  [false; false; true;false; true; false]).
  {
    assert(Some x = Some [false; false; true;false; true; false] -> x = [false; false; true;false; true; false]).
    {
      intros H'. apply some_stuff_eq_other. rewrite H'. reflexivity.
    }
    rewrite H0. reflexivity.
    rewrite H. reflexivity.
  }
  rewrite H0. compute. reflexivity.
Qed.
