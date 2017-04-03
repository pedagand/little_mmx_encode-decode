Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encodeProof Mmx.decodeProof Mmx.encode.


(* Proof about encode_decode_flux *)

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



(* Some proofs about cut32 and concatlistes *)




(* good proofs *)  
Lemma app_cut32 : forall (l1 l2 : list bool) (ll : list (list bool)), length l1 = 32 -> cut32 l2 = Some ll
                                                                      -> cut32 (l1 ++ l2) = Some (l1 :: ll).
Proof.
  intros.
  unfold cut32.
  assert (length (l1 ++ l2) mod 32 =? 0 = true).
  {
    rewrite app_length.
    rewrite H.
    Search ((_ + _) mod _).
    rewrite Nat.add_mod.    
    -{
        Search (_ mod _ = 0).
        rewrite Nat.mod_same.
        -Search (0 + _).
         rewrite plus_O_n.
         unfold cut32 in H0.
         destruct (length l2 mod 32).
         +reflexivity.
         +discriminate.
        -auto.
     }
    -auto.
  }
  rewrite H1.
  assert(length (l1 ++ l2) / 32 = S (length l2 / 32)).
  {
    rewrite app_length.
    rewrite H.
    Check Nat.div_add_l.
    specialize (Nat.div_add_l 1 32 (length l2)).
    intros.
    Search (1 * _).
    rewrite Nat.mul_1_l in H2.
    apply H2.
    auto.    
  }  
  rewrite H2.
  unfold cut32_n.
  assert (firstn 32 (l1 ++ l2) = l1).
  {
    Search (_ = _ -> _ <= _).
    Search firstn.
    Check firstn_app_2.
    rewrite <- H.
    Search (_ + 0).
    specialize (plus_n_O (length l1)).
    intros.
    rewrite H3.
    Check firstn_app_2.
    specialize (firstn_app_2 0 l1 l2).
    intros.
    rewrite H4.
    simpl.
    Search (_ ++ []).
    apply app_nil_r.
  }
  rewrite H3.
  fold cut32_n.
  Search (_ :: _ = _ :: _).
  assert (forall (l1 l2: list (list bool)), l1 = l2 -> Some l1 = Some l2).
  {
    intros.
    rewrite H4.
    reflexivity.
  }
  apply H4.
  Check delete_concat.
  assert (forall (lb : list bool) (ll1 ll2 : list (list bool)), ll1 = ll2 -> lb :: ll1 = lb :: ll2).
  {
    intros.
    rewrite H5.
    reflexivity.
  }
  apply H5.
  unfold cut32 in H0.
  assert (length l2 mod 32 =? 0 = true).
  {
    destruct (length l2 mod 32).
    -reflexivity.
    -simpl in H0.
     discriminate.
  }
  rewrite H6 in H0.
  assert (skipn 32 (l1 ++ l2) = l2).
  {
    SearchAbout skipn.
    assert (firstn 32 (l1 ++ l2) ++ skipn 32 (l1 ++ l2) = (l1 ++ l2)).
    {
      apply firstn_skipn.
    }
    rewrite H3 in H7.
    Search (_ ++ _ = _ ++ _).
    apply app_inv_head in H7.
    auto.
  }
  rewrite H7.
  inversion H0.
  assert (forall (n : nat), n / 32 = fst (Nat.divmod n 31 0 31)).
  {
    destruct n.
    -reflexivity.
    -reflexivity.
  }
  rewrite H8.
  reflexivity.
Qed.
  
Lemma concat_listes_cut32 : forall (ll : list (list bool)) (l : list bool) ,
    concat_listes_32 ll = Some l -> cut32 l = Some ll.
Proof.
  assert (I : forall (ll : list (list bool)) (l : list bool), concat_listes_32 ll = Some l -> cut32 l = Some ll).
  {
    induction ll.
    -assert (I_1 : forall l : list bool, concat_listes_32 [] = Some l -> cut32 l = Some []).
     {
       intros.
       simpl in H.
       inversion H.
       reflexivity.
     }
     auto.
    -assert(forall l : list bool, concat_listes_32 (a :: ll) = Some l -> cut32 l = Some (a :: ll)).
     {
       intros.
       unfold concat_listes_32 in H.
       apply bind_rewrite in H.
       destruct H.
       destruct H.
       fold concat_listes_32 in H0.
       destruct (length a =? 32) eqn:H1.
       -{
           inversion H.
           specialize (IHll x).
           apply commut_equal in H0.
           apply IHll in H0.
           Check app_cut32.
           apply app_cut32.           
           -apply beq_nat_true in H1.
            auto.
           -auto.
         }
       -discriminate.
     }
     auto.
  }
  auto.
Qed.           


Lemma cut32_concat_listes : forall  (ll : list (list bool)) (l : list bool),
    cut32 l = Some ll -> concat_listes_32 ll = Some l.
Proof.
  Admitted.



(* Finals goal of this file, proofs about encode_flux_b and decode_flux_b *)

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
   rewrite H.
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




