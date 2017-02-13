Require Import Bool List Arith Nat.
Import ListNotations.

Fixpoint bit_n (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => (if a then 1 else 0) + (2 * bit_n tl)
  end.

Definition testList := [ false ; false ; true ; false].
Compute bit_n testList.

Fixpoint n_bit (n : nat) (k : nat) : option (list bool) :=
  if beq_nat k 0 then Some []
  else
    match n with
      | 0 => if ltb k 1 then Some [] else None
      | S n' => match n_bit n' (div k 2) with
                  | None => None
                  | Some l => Some ((beq_nat (modulo k 2) 1) :: l)
                end
    end.

Compute n_bit 32 6.
Compute bit_n (match (n_bit 32 6) with Some x => x | None => [] end).
Compute bit_n (match (n_bit 12 0) with Some x => x | None => [] end).
Compute bit_n [true;true;false].



Theorem n_bit_n : forall (l : list bool) (n k : nat),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (l : list bool) (n k : nat), n_bit n k = Some l -> bit_n l = k).
  {
    intros l n k.
    induction k.
    assert (I_1 : n_bit n 0 = Some l -> bit_n l = 0).
    {
      assert (I_1_1 : n_bit n 0 = Some []).
      {
        destruct n.
        -reflexivity.
        -reflexivity.
      }
      rewrite I_1_1.
      intros H.
      inversion H.
      reflexivity.
    }
    exact I_1.
    assert (I_2 : n_bit n (S k) = Some l -> bit_n l = S k).
    {
      assert (I_2_1 : n_bit n (S k) = Some l -> l = 
      destruct n.
      -discriminate.
      -
    }
    
    
    

    
    intros l n k.
    intro H.
    induction l.
    assert (I_1 : bit_n [] = k).
    {
      simpl.
      destruct k.
      -reflexivity.
      -assert (I_2 : n_bit n (S k) = Some [] -> False).
       {
         admit.
       }
       apply False_ind.
       apply I_2.
       exact H.
    }
    exact I_1.
    assert (I_2 : bit_n (a :: l) = k).
    {
      rewrite H in IHl.
    }
    exact I_2.
  }
  exact I.
  }










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
      -reflexivity.
       (* the hypothesis is false so we will need to find how to demonstrate this *)
      -assert (I_1_1 : n_bit n (S k) = Some [] -> bit_n [] = S k).
       {
         admit.
       }
       exact I_1_1.
    }
    exact I_1.
    assert (I_2 : n_bit n k = Some (a :: l) -> bit_n (a :: l) = k).
    {
      intros H.
      destruct a.
      simpl.
      assert (I_2_1 : S (bit_n l + (bit_n l + 0)) = k).
      {
        Search (_ + 0 = _).
        rewrite Nat.add_0_r.
        apply False_ind.
        Search (S (_ + _)).
      }



                
      induction k.
      assert (I_2_1 : n_bit n 0 = Some (a :: l) -> bit_n (a :: l) = 0).
      {
        assert (I_2_1_1 : n_bit n 0 = Some []).
        {
          induction n.
          -reflexivity.
          -reflexivity.
        }
        rewrite I_2_1_1.
        intros H.
        discriminate.
      }
      exact I_2_1.
      assert (I_2_2 : n_bit n (S k) = Some (a :: l) -> bit_n (a :: l) = S k).
      {
        destruct n.
        assert (I_2_2_1 : n_bit 0 (S k) = Some (a :: l) -> bit_n (a :: l) = S k).
        {
          simpl.
          intros H.
          discriminate.
        }
        exact I_2_2_1.
        assert (I_2_2_2 : n_bit (S n) (S k) = Some (a :: l) -> bit_n (a :: l) = S k).
        {
          assert (I_2_2_2_1 : n_bit n (S k) = Some l -> n_bit (S n) (S k) = Some l).
          {
            admit.
          }
          intros H.
          rewrite I_2_2_2_1 in H.
          inversion H.
          rewrite <- H1. rewrite <- H1.
          apply IHl.
          apply I_2_2_2_1.
          admit. admit.
        }
        exact I_2_2_2.                  
      }
      exact I_2_2.
    }
    exact I_2.
  }
  exact I.