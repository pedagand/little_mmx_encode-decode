Require Import Bool List Arith Nat.
Import ListNotations.

Fixpoint bit_n (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => 2 * bit_n tl + Nat.b2n a
  end.

Definition testList := [ true ; false ; true ].
Compute bit_n testList.

Definition bit_n_vrai (l : list bool) :=
  bit_n (rev l).

Definition testList' := [ true ; false ; false ].
Compute bit_n_vrai testList'.

Fixpoint n_bit (n : nat) (k : nat) : option (list bool) :=
    match n with
      | 0 => match k with
             | 0 => Some []
             | S _ => None
             end
      | S n' => match n_bit n' (Nat.div2 k) with
                  | None => None
                  | Some l => Some (Nat.odd k :: l)
                end
    end.

Definition testListe'' := [true;false; false ; false].
Compute n_bit 32 6.
Compute bit_n (match (n_bit 32 6) with Some x => x | None => [true] end).
Compute bit_n (match (n_bit 12 55) with Some x => x | None => [true] end).
Compute bit_n (match (n_bit 12 0) with Some x => x | None => [true] end).
Compute n_bit 4 (bit_n testListe'').
Compute bit_n [true;true;false].


Function true_in_list (l : list bool) : bool :=
  match l with
    | [] => false
    | h :: tl => if h then true else true_in_list tl
  end.


Theorem n_bit_n : forall (l : list bool) (n k : nat),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (l : list bool) (n k : nat), n_bit n k = Some l -> bit_n l = k).
  {
    intros l; induction l; intros n k.
    simpl.
    assert (I_1 : n_bit n k = Some [] -> bit_n [] = k).
    {
      induction k.
      - reflexivity.
       (* the hypothesis is false so we will need to find how to demonstrate this *)
      - assert (I_1_1 : n_bit n (S k) = Some [] -> bit_n [] = S k).
       {
         induction n.
         - discriminate.
         - unfold n_bit; fold n_bit.
           destruct (n_bit n (Nat.div2 (S k))); discriminate.
       }
       exact I_1_1.
    }
    exact I_1.
    assert (I_2 : n_bit n k = Some (a :: l) -> bit_n (a :: l) = k).
    {
      intros H.
      simpl.
      rewrite (Nat.div2_odd k).
      simpl.
      destruct n; simpl in H.
      - destruct k; discriminate.
      - destruct (n_bit n (Nat.div2 k)) eqn:Hl; try discriminate.
        inversion H; subst.
        erewrite IHl; eauto.
    }
    assumption.
  }
  assumption.
Qed.