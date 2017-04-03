Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encodeProof Mmx.decodeProof Mmx.encode.


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


