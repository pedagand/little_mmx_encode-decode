Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encodeProof Mmx.decodeProof Mmx.encode.


Print encode_flux.



Lemma encode_decode_decoup_flux_decoup : forall (lb : list binary_instruction) (l : list instruction),
    encode_flux l = Some lb -> decode_flux_decoup lb = Some l.
Proof.
  induction lb.
  -intros.
   unfold encode_flux in H.
   assert (traverse (encode_flux_opt l) = Some [] -> l = []).
   {
     destruct l.
     -reflexivity.
     -simpl.
      destruct (encode i).
      +destruct (traverse (encode_flux_opt l)).
       discriminate.
       discriminate.
      +discriminate.
   }
   apply H0 in H.
   rewrite H.
   auto.
  -destruct l.
   +unfold encode_flux.
    simpl.
    discriminate.
   +intros.
    assert (keep : encode_flux (i :: l) = Some (a :: lb)) by auto.
    assert (encode_flux (i :: l) = Some (a :: lb) -> encode i = Some a).
    {
      unfold encode_flux.
      simpl.
      intros.
      destruct (encode i).
      assert (encode_flux (i :: l) = Some (a :: lb) -> encode_flux l = Some lb).
      {
        unfold encode_flux.
        simpl.
        intros.
        destruct (encode i).
        -destruct (traverse (encode_flux_opt l)).
         +inversion H1.
          reflexivity.
         +discriminate.
        -discriminate.
      }
      apply H1 in H.
      assert (traverse (encode_flux_opt l) = encode_flux l).
      {
        unfold encode_flux.
        reflexivity.
      }
      rewrite H2 in H0.
      rewrite H in H0.
      -inversion H0.
       reflexivity.
      -discriminate.
    }
    apply H0 in H.
    unfold decode_flux_decoup.
    simpl.
    apply encode_decode in H.
    rewrite H.
    fold decode_flux_decoup.
    assert (traverse (decode_flux_opt lb) = decode_flux_decoup lb).
    {
      unfold decode_flux_decoup.
      reflexivity.
    }
    rewrite H1.
    assert (decode_flux_decoup lb = Some l).
    {
      apply IHlb.
      assert (encode_flux (i :: l) = Some (a :: lb) -> encode_flux l = Some lb).
      {
        unfold encode_flux.
        simpl.
        intros.
        destruct (encode i).
        -destruct (traverse (encode_flux_opt l)).
         +inversion H2.
          reflexivity.
         +discriminate.
        -discriminate.
      }
      apply H2 in keep.
      auto.                   
    }
    rewrite H2.
    reflexivity.
Qed.


Lemma decode_decoup_encode_flux : forall (l : list instruction) (lb : list binary_instruction),
    decode_flux_decoup lb = Some l -> encode_flux l = Some lb.
Proof.
  induction l.
  -unfold decode_flux_decoup.
   unfold encode_flux.
   intros.
   assert (traverse (decode_flux_opt lb) = Some [] -> lb = []).
   {
     destruct lb.
     -reflexivity.
     -simpl.
      destruct (decode b).
      +destruct (traverse (decode_flux_opt lb)).
       discriminate.
       discriminate.
      +discriminate.
   }
   apply H0 in H.
   rewrite H.
   reflexivity.
  -intros.
   destruct lb.
   +unfold decode_flux_decoup in H.
    simpl in H.
    discriminate.
   +assert (keep : decode_flux_decoup (b :: lb) = Some (a :: l)) by auto.
    assert (keep2 : decode_flux_decoup (b :: lb) = Some (a :: l)) by auto.
    assert (decode_flux_decoup (b :: lb) = Some (a :: l) -> decode_flux_decoup lb = Some l).
    {
      unfold decode_flux_decoup.
      intros.
      simpl in H0.
      destruct (decode b).
      -destruct (traverse (decode_flux_opt lb)).
       +inversion H0.
        reflexivity.
       +discriminate.
      -discriminate.
    }
    apply H0 in H.
    unfold encode_flux.
    simpl.
    assert (decode_flux_decoup (b :: lb) = Some (a :: l) -> decode b = Some a).
    { 
      intros.
      unfold decode_flux_decoup in H1.
      simpl in H1.
      destruct (decode b).
      -destruct (traverse (decode_flux_opt lb)).
       +inversion H1.
       reflexivity.
       +discriminate.
      -discriminate.
    }
    apply H1 in keep.
    Search decode.
    apply decode_encode in keep.
    {
      rewrite keep.
      assert (traverse (encode_flux_opt l) = encode_flux l).
      {
        unfold encode_flux.
        reflexivity.
      }
      rewrite H2.
      assert (encode_flux l = Some lb).
      {
        apply IHl.
        auto.        
      }
      rewrite H3.
      reflexivity.
    }    
    assert (decode_flux_decoup (b :: lb) = Some (a :: l) -> length b = 32).
    {
      unfold decode_flux_decoup.
      simpl.
      intros.
      Search decode.
      Check decode_size.
      apply decode_size in keep.
      auto.
    }
    apply H2 in keep2.
    auto.
Qed.

Lemma div_S_n : forall (n m q : nat), n / m = S q -> m <= n.
Proof.
  intros.
  apply Nat.div_str_pos_iff.
  -destruct m.
   +discriminate.
   +auto.
  -rewrite H.
   apply Nat.lt_0_succ.
Qed.
   
Lemma cut32_not_useful_now : forall (l l': list bool) (ll : list (list bool)),
    cut32 l = Some (l' :: ll) -> length l' = 32.
Proof.
  intros.
  unfold cut32 in H.
  destruct (length l mod 32 =? 0) eqn:H1.
  -destruct (length l / 32) eqn:H2.
   +simpl in H.
    discriminate.
   +unfold cut32_n in H.
    fold cut32_n in H.
    assert (32 <= length l) by (specialize (div_S_n (length l) 32 n);auto).
    assert (forall (l1 l2: list bool) (tl1 tl2 : list (list bool)), Some (l1 :: tl1) = Some (l2 :: tl2) -> l1 = l2).
    { intros. inversion H3. reflexivity. }
    apply H3 in H.
    rewrite <- H.
    Search firstn.
    apply firstn_length_le.
    auto.
  -discriminate.
Qed.

    
(* Lemma cut32_check_length_32' : forall (l : list bool) (ll : list (list bool)), *)
(*     cut32 l = Some ll -> check_length_32 ll = true. *)
(* Proof. *)
(*   induction l. *)
(*   -intros. *)
(*    unfold cut32 in H. *)
(*    simpl in H. *)
(*    inversion H. *)
(*    reflexivity. *)
(*   -intros. *)
(*    unfold cut32 in H. *)
(*    destruct (length (a :: l) mod 32 =? 0) eqn:H1. *)
(*    +unfold cut32_n in H. *)
(*     destruct (length (a :: l) / 32) eqn:H2. *)
(*     { inversion H. reflexivity. } *)
(*     { fold cut32_n in H. *)
(*       assert (forall (l1: list bool) (l2 tl1 : list (list bool)), Some (l1 :: tl1) = Some l2 -> l2 = l1 :: tl1). *)
(*       { intros. inversion H0. reflexivity. } *)
(*       apply H0 in H. *)
(*       unfold check_length_32. *)
    
(*    +discriminate. *)


(* Lemma cut32_check_length_32 : forall (ll : list (list bool)) (l : list bool), *)
(*     cut32 l = Some ll -> check_length_32 ll = true. *)
(* Proof.   *)
(*   induction ll. *)
(*   -intros. *)
(*    reflexivity. *)
(*   -intros. *)
(*    assert (length a =? 32 = true). *)
(*    { *)
(*      unfold cut32 in H. *)
(*      destruct (length l mod 32 =? 0) eqn:H1. *)
(*      -Search (_ mod _). *)
(*       destruct (length l / 32) eqn:H2. *)
(*       +discriminate. *)
(*       +assert (32 <= length l) by (specialize (div_S_n (length l) 32 n);auto). *)
(*        unfold cut32_n in H. *)
(*        fold cut32_n in H. *)
(*        assert (a = firstn 32 l). *)
(*        { *)
(*          fold cut32_n in H. *)
(*          assert (forall (l1 l2: list bool) (tl1 tl2 : list (list bool)), Some (l1 :: tl1) = Some (l2 :: tl2) -> l1 = l2). *)
(*          { *)
(*            intros. *)
(*            inversion H3. *)
(*            reflexivity. *)
(*          } *)
(*          apply H3 in H. *)
(*          auto. *)
(*        } *)
(*        rewrite H3. *)
(*        Search firstn. *)
(*        assert (length (firstn 32 l) = 32) by (apply firstn_length_le;auto). *)
(*        rewrite H4. *)
(*        reflexivity. *)
(*      -discriminate. *)
(*    } *)
   
   


   
(*    unfold check_length_32. *)
(*    rewrite H0. *)
(*    simpl. *)
(*    fold check_length_32. *)
(*    specialize (IHll l). *)
(*    apply IHll. *)
(*    unfold cut32 in H. *)
(*    destruct (length l mod 32 =? 0) eqn:Hl1. *)
(*    +Search (_ mod _). *)
(*    +discriminate. *)
(*    assert (cut32 l = Some (a :: ll) -> length a = 32). *)
(*    { *)
(*      unfold cut32. *)
(*      destruct (length l mod 32 =? 0). *)
(*      -unfold cut32_n. *)
(*       destruct (length l / 32). *)
(*       +discriminate. *)
(*       + *)
(*    } *)

Lemma check_length_true : forall (l : list bool) (ll : list (list bool)), check_length_32 (l :: ll) = true -> length l = 32.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  apply beq_nat_true in H.
  auto.
Qed.

Lemma concat_listes_prop : forall (ll : list (list bool)) (l : list bool), concat_listes_32 ll = Some l -> (length l) mod 32 = 0.
Proof.
  induction ll.
  -intros.
   simpl in H.
   inversion H.
   reflexivity.
  -intros.
   unfold concat_listes_32 in H.
   apply bind_rewrite in H.
   destruct H.
   destruct H.
   destruct (length a =? 32) eqn:H1.
   +fold concat_listes_32 in H0.
    specialize (IHll x).
    apply commut_equal in H0.
    apply IHll in H0.
    inversion H.
    Search (length (_ ++ _)).
    rewrite app_length.
    rewrite Nat.add_mod.
    {
      rewrite H0.
      Search (_ + 0).
      rewrite <- plus_n_O.
      Search ((_ =? _) = true).
      apply beq_nat_true in H1.
      rewrite H1.
      Search (_ mod _ = 0).
      rewrite Nat.mod_same.
      -reflexivity.
      -auto.
    }    
    auto.
   +discriminate.
Qed.

Lemma concat_listes_cut32 : forall (ll : list (list bool)) (l : list bool) ,
    check_length_32 ll = true -> concat_listes_32 ll = Some l -> cut32 l = Some ll.
Proof.
  induction ll.
  -intros.
   unfold concat_listes_32 in H0.
   inversion H0.
   reflexivity.
  -intros.
   simpl in H0.
   apply bind_rewrite in H0.
   destruct H0.
   destruct H0.
   Search check_length_32.
   assert (length a = 32).
   { apply check_length_true in H. auto. }
   rewrite H2 in H0.
   simpl in H0.
   inversion H0.
   unfold cut32.
   assert (length (a ++ x) mod 32 = 0).
   {
     rewrite app_length.
     assert (keep : check_length_32 (a :: ll) = true) by auto.
     apply check_length_true in keep.
     rewrite keep.
     Search ((_ + _) mod _).
     rewrite Nat.add_mod.
     assert (32 mod 32 = 0).
     { apply Nat.mod_same. auto. }
     rewrite H3.
     rewrite plus_O_n.     
     apply commut_equal in H1.
     Check concat_listes_prop.
     apply concat_listes_prop in H1.
     rewrite H1.
     reflexivity.
     auto.
   }
   rewrite H3.
   simpl.
   assert (32 <= length (a ++ x)).
   {
     admit.
   }
   destruct (length (a ++ x)) eqn:lol.
   +Search (_ <= 0).
    apply Nat.nle_succ_0 in H5.
    inversion H5.
   +destruct (fst (Nat.divmod (S n) 31 0 31)) eqn:test.
    {
      Search Nat.divmod.
      assert (0 <= S n) by apply Peano.le_0_n.
      Search Nat.divmod.    
      Search (_ / _).
      specialize (Nat.div_str_pos (S n) 32).
      intros.
      assert (0 < 32 <= S n).
      {
        Search (S _ <= _).
        Search (0 < S _).
        assert (0 < 32) by apply Nat.lt_0_succ.
        assert (32 <= S n).
        {
          auto.
        }
        auto.    
      }
      apply H7 in H8.
      assert (S n / 32 = fst (Nat.divmod (S n) 31 0 31)) by reflexivity.
      rewrite H9 in H8.
      rewrite test in H8.
      Search (_  < 0).
      apply Nat.nlt_0_r in H8.
      inversion H8.
    }
    unfold cut32_n.
    fold cut32_n.
    assert (firstn 32 (a ++ x) = a) by admit.
    rewrite H6.
    assert (Some (cut32_n n0 (skipn 32 (a ++ x))) = Some ll -> Some (a :: cut32_n n0 (skipn 32 (a ++ x))) = Some (a :: ll)) by admit.
    apply H7.
    assert (skipn 32 (a ++ x) = x) by admit.
    rewrite H8.
    assert (forall (n' : nat),n' = (length x / 32) -> cut32 x = Some ll -> Some (cut32_n n' x) = Some ll).
    {
      induction n'.
      -intros.
       unfold cut32 in H10.
       destruct (length x mod 32 =? 0) eqn:tryH.
       +rewrite H9.
        auto.
       +discriminate.
      -intros.
       assert (forall (ll ll2 : list (list bool)), ll = ll2 -> Some ll = Some ll2) by admit.
       apply H11.
       unfold cut32_n.
       fold cut32_n.
       destruct ll.
       admit.
       admit.
    }
    
    apply H9.
    {
      simpl in test.
      admit.
    }
    apply IHll.
    assert (check_length_32 (a :: ll) = true -> check_length_32 ll = true).
    {
      intros.
      simpl in H.
      rewrite H2 in H.
      simpl.
      auto.
    }
    apply H10 in H.
    auto.
    apply commut_equal in H1.
    auto.
    Admitted.
    
    

    
    
   
   
    
  intros.  
  unfold concat_listes_32 in H0.
  destruct ll eqn:HL1.
  -inversion H0.
   reflexivity.
  -assert (keep : check_length_32 (l0 :: l1) = true) by auto.
   fold concat_listes_32 in H0.   
   apply bind_rewrite in H0.
   destruct H0.
   apply check_length_true in H.
   rewrite H in H0.
   simpl in H0.
   destruct H0.
   inversion H0.
   fold concat_listes_32 in H1.
   unfold cut32.
   assert (length (l0 ++ x) mod 32 = 0).
   {
     rewrite app_length.
     apply check_length_true in keep.
     rewrite keep.
     Search ((_ + _) mod _).
     rewrite Nat.add_mod.
     assert (32 mod 32 = 0).
     { apply Nat.mod_same. auto. }
     rewrite H2.
     rewrite plus_O_n.     
     apply commut_equal in H1.
     Check concat_listes_prop.
     apply concat_listes_prop in H1.
     rewrite H1.
     reflexivity.
     auto.
   }
   rewrite H2.
   simpl.
   unfold cut32_n.
Admitted.
   
   (* la il me faut un truc du style vus que avec le modulo je montre que c'est plus grand alors je peux montrer que length lol / 32 
est egale a S n ce qui me fait une étape de calcule et après après la truc de récurence ça devrait passer :p *)

   


(* (* need theese 2 lemma to make the final proof *) *)
(* Lemma concat_listes_cut32' : forall (l : list bool) (ll : list (list bool)), *)
(*     concat_listes_32 ll = Some l -> cut32 l = Some ll. *)
(* Proof. *)
(*   induction l. *)
(*   -intros. *)
(*    assert (concat_listes_32 ll = Some [] -> ll = []). *)
(*    { *)
(*      destruct ll. *)
(*      -reflexivity. *)
(*      -simpl. *)
(*       destruct l. *)
(*       +discriminate. *)
(*       +simpl in H. *)
(*        apply bind_rewrite in H. *)
(*        destruct H. *)
(*        destruct H. *)
(*        discriminate. *)
(*    } *)
(*    apply H0 in H. *)
(*    rewrite H. *)
(*    reflexivity. *)
(*   -intros. *)
(*    unfold cut32. *)
(* Admitted. *)




Lemma concat_listes_check_length : forall (ll : list (list bool)) (l : list bool), concat_listes_32 ll = Some l -> check_length_32 ll = true.
Proof.
  induction ll.
  -reflexivity.
  -intros.
   assert (keep : concat_listes_32 (a :: ll) = Some l) by auto.
   unfold concat_listes_32 in H.
   apply bind_rewrite in H.
   destruct H.
   Search concat_listes_32.
   destruct (length a =? 32) eqn:H1.
   +destruct H.
    fold concat_listes_32 in H0.
    specialize (IHll x).
    simpl.
    rewrite H1.
    simpl.
    apply IHll.
    auto.
   +destruct H.
    discriminate.
Qed.
   



  
(* now theese are the real theorems *)
Lemma encode_decode_flux_decoup : forall (lb : list bool) (l : list instruction),
    encode_flux_b l = Some lb -> decode_flux lb = Some l.
Proof.
  intros.
  unfold encode_flux_b in H.
  destruct encode_flux eqn:H1.
  -Search (encode_flux).
   apply encode_decode_decoup_flux_decoup in H1.
   unfold decode_flux.
   Search concat_listes_32.
   apply concat_listes_cut32 in H.
   +rewrite H.
    auto.
   +apply concat_listes_check_length in H.
    auto.  
  -discriminate.
Qed.


Lemma decode_flux_decoup_encode : forall (lb : list bool) (l : list instruction), 
    decode_flux lb = Some l -> encode_flux_b l = Some lb.
Proof.
  intros.
  unfold decode_flux in H.
  unfold encode_flux_b.
  destruct (cut32 lb) eqn:H1.
  -simpl in H. Search (decode_flux_decoup).
   apply decode_decoup_encode_flux in H.
   rewrite H.
   Search cut32.
   apply cut32_concat_listes in H1.
   rewrite H1.
   reflexivity.
  -simpl in H.
   discriminate.
Qed.  

   
  
    
 



  
   
   

