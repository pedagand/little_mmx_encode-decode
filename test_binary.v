Require Import Bool List Arith Nat.
Import ListNotations.

Fixpoint bit_n (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => (if a then 1 else 0) + (2 * bit_n tl)
  end.

Definition testList := [ true ; false ; true ].
Compute bit_n testList.

Definition bit_n_vrai (l : list bool) :=
  bit_n (rev l).

Definition testList' := [ true ; false ; false ].
Compute bit_n_vrai testList'.

Fixpoint n_bit (n : nat) (k : nat) : option (list bool) :=
    match n with
      | 0 => if ltb k 1 then Some [] else None
      | S n' => match n_bit n' (div k 2) with
                  | None => None
                  | Some l => Some ((beq_nat (modulo k 2) 1) :: l)
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

Theorem bit_n_bit : forall (l : list bool) (n : nat),
                      n = length l -> (n_bit n (bit_n l)) = Some l.
Proof.
  assert (I : forall (l : list bool) (n : nat), n = length l -> n_bit n (bit_n l) = Some l).
  {
    induction l.
    -simpl.
     intros n H.
     rewrite H.
     reflexivity.
    -intros n H.
     simpl.
     destruct a.
     +simpl.
     
     
     
     
  }



Theorem n_bit_n : forall  (l : list bool) (n k : nat),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall  (l : list bool) (n k : nat), n_bit n k = Some l -> bit_n l = k).
  {
    induction l.
    assert (I_1 : forall n k : nat, n_bit n k = Some [] -> bit_n [] = k).
    {
      admit.
    }
    exact I_1.
    assert (I_2 : forall n k : nat, n_bit n k = Some (a :: l) -> bit_n (a :: l) = k).
    {
      admit.
    }
    exact I_2.
  }
  exact I.
Admitted.
Theorem n_bit_n' : forall (n k : nat) (l : list bool),
                     n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (n k : nat) (l : list bool), n_bit n k = Some l -> bit_n l = k).
  {
    induction n.
    assert (I_1 : forall (k : nat) (l : list bool), n_bit 0 k = Some l -> bit_n l = k).
    {
      admit.
    }
    exact I_1.
    assert (I_2 : forall (k : nat) (l : list bool), n_bit (S n) k = Some l -> bit_n l = k).
    {
      admit.
    }
    exact I_2.
  }
  exact I.
Admitted.


Theorem n_bit_n'' : forall (k n : nat) (l : list bool),
                     n_bit n k = Some l -> bit_n l = k.
Proof.
  assert(I : forall (k n : nat) (l : list bool), n_bit n k = Some l -> bit_n l = k).
  {
    induction k.
    assert (I_1 : forall (n : nat) (l : list bool), n_bit n 0 = Some l -> bit_n l = 0).
    {
      induction l.
      assert (I_1_1 : n_bit n 0 = Some [] -> bit_n [] = 0).
      {
        reflexivity.
      }
      exact I_1_1.
      assert (I_1_2 : n_bit n 0 = Some (a :: l) -> bit_n (a :: l) = 0).
      {
        induction n.
        assert (I_1_2_1 : n_bit 0 0 = Some (a :: l) -> bit_n (a :: l) = 0).
        {
          simpl.
          intros H.
          discriminate.
        }
        exact I_1_2_1.
        assert (I_1_2_2 : n_bit (S n) 0 = Some (a :: l) -> bit_n (a :: l) = 0).
        {
          assert (I_1_2_2_1 : forall n' l', length l' = n' -> n_bit (S n') 0 = Some (false :: l')).
          {
            intros n' l' H.
            induction n'.
            -simpl.
             apply length_zero_iff_nil in H.
             rewrite H.
             reflexivity.
            -
          }
          destruct a.

        }
      }
    }
    exact I_1.
    assert (I_2 : forall (n : nat) (l : list bool), n_bit n (S k) = Some l -> bit_n l = S k).
    {
      admit.      
    }
    exact I_2.
  }
  exact I.






Theorem n_bit_n : forall (n k : nat) (l : list bool),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (n k: nat) (l : list bool), n_bit n k = Some l -> bit_n l = k).
  {
    (* induction n. *)
    (* assert (I_1 : forall (k : nat) (l : list bool), n_bit 0 k = Some l -> bit_n l = k). *)
    (* { *)
    (*   induction k. *)
    (*   assert (I_1_1 : forall l : list bool, n_bit 0 0 = Some l -> bit_n l = 0). *)
    (*   { *)
    (*     simpl. *)
    (*     intros l H. *)
    (*     inversion H. *)
    (*     simpl. *)
    (*     reflexivity. *)
    (*   } *)
    (*   exact I_1_1. *)
    (*   assert (I_1_2 : forall l : list bool, n_bit 0 (S k) = Some l -> bit_n l = S k). *)
    (*   { *)
    (*     intros l. *)
    (*     simpl. *)
    (*     intros H. *)
    (*     discriminate. *)
    (*   } *)
    (*   exact I_1_2. *)
    (* }     *)
    (* exact I_1. *)
    (* assert (I_2 : forall (k : nat) (l : list bool), n_bit (S n) k = Some l -> bit_n l = k). *)
    (* { *)
    (*   intros k l. *)
    (*   intros H. *)
    (*   induction k. *)
    (*   assert (I_2_1 : bit_n l = 0). *)
    (*   { *)
    (*     assert (I_2_1_2 : n_bit (S n) 0 = Some []). *)
    (*     { *)
          
    (*     } *)
    (*   } *)
    (* } *)
Admitted.






(* fail again *)
Theorem n_bit_n' : forall (k n : nat) (l : list bool),
                    n_bit n k = Some l -> bit_n l = k.
Proof.
  assert (I : forall (k n: nat) (l : list bool), n_bit n k = Some l -> bit_n l = k).
  {    
    induction k.
    assert (I_1 : forall (n : nat) (l : list bool), n_bit n 0 = Some l -> bit_n l = 0).
    {
      intros n l.
      intros H.
      induction n.
      -simpl.
       simpl in H.
       inversion H.
       reflexivity.
      -induction l.
       +reflexivity.
       +destruct a.
        {
          admit.          
        }
        {
          assert (I_1_2 : bit_n (false :: l) = 0).
          {
            assert (I_1_2_1 : forall l', bit_n l' = 0 -> bit_n (false :: l') = 0).
            {
              intros l' H'.
              induction l'.
              -reflexivity.              
              -destruct a.
               +simpl.
                discriminate.
               +assert (I_1_2_1_1 : forall l'', bit_n (false :: l'') = 2 * (bit_n l'')).
                {
                  intros l''.
                  simpl. reflexivity.
                }
                rewrite I_1_2_1_1.
                rewrite H'.
                reflexivity.
            }
            rewrite I_1_2_1.
            reflexivity.
            

            
          }
        }
         
                   
    }












      
      intros n l.
      assert (I_1_1 : n_bit n 0 = Some l -> bit_n l = 0).
      {
        assert (I_1_1_2 : n_bit n 0 = Some l -> true_in_list l = false).
        {
          induction n.
          assert (I_1_1_2_1 : n_bit 0 0 = Some l -> true_in_list l = false).
          {
            simpl.
            intros H.
            inversion H.
            reflexivity.
          }
          exact I_1_1_2_1.
          assert (I_1_1_2_2 : n_bit (S n) 0 = Some l -> true_in_list l = false).
          {
            
          }
        }
      }












      
      assert (I_1_1 : n_bit n 0 = Some []).
      {
        induction n.
        -reflexivity.
        -assert (I_1_1_1 : n_bit (S n) 0 = Some []).
         {
           simpl. rewrite IHn.
           (* ici j'abandonne cette preuve car ce cas est impossible, l'induction sur n me semble impossible 
            sauf si je rajoute dans n_bit un test pour si k = 0 => [] alors ça marche mais on a plus des listes de bonne taille*)
         }
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