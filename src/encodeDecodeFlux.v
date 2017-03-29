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

Lemma cut32_check_length_32 : forall (ll : list (list bool)) (l : list bool),
    cut32 l = Some ll -> check_length_32 ll = true.
Proof.
  induction ll.
  -intros.
   reflexivity.
  -intros.
   assert (cut32 l = Some (a :: ll) -> length a = 32).
   {
     unfold cut32.
     destruct (length l mod 32 =? 0).
     -unfold cut32_n.
      destruct (length l / 32).
      +discriminate.
      +Search (firstn).
   }


Lemma concat_listes_cut32 : forall (l : list bool) (ll : list (list bool)),
    check_length_32 ll = true -> concat_listes ll = l -> cut32 l = Some ll.
Proof.
  induction l.
  -intros.
   assert (concat_listes ll = [] -> ll = []).
   {
     unfold check_length_32 in H.
     unfold concat_listes ll.
   }
Admitted.

Fixpoint concat_listes' (l : list (list bool)) : option (list bool) :=
  match l with
  | [] => Some []
  | [] :: tl => None
  | h :: tl => let! res := (concat_listes' tl) in fun res => Some (h ++ res)
  end.

(* need theese 2 lemma to make the final proof *)
Lemma concat_listes'_cut32 : forall (l : list bool) (ll : list (list bool)),
    concat_listes' ll = Some l -> cut32 l = Some ll.
Proof.
  induction l.
  -intros.
   assert (concat_listes' ll = Some [] -> ll = []).
   {
     destruct ll.
     -reflexivity.
     -simpl.
      destruct l.
      +discriminate.
      +simpl in H.
       apply bind_rewrite in H.
       destruct H.
       destruct H.
       discriminate.
   }
   apply H0 in H.
   rewrite H.
   reflexivity.
  -intros.
   unfold cut32.
Admitted.


Lemma cut32_concat_listes : forall  (ll : list (list bool)) (l : list bool),
    cut32 l = Some ll -> concat_listes ll = l.
Proof.
  induction ll.
  -simpl.
   intros.
   assert (cut32 l = Some [] -> l = []).
   {
     induction l.
     -reflexivity.
     -intros.
      unfold cut32 in H0.
      destruct (length (a :: l)) eqn:H1.
      +apply length_zero_iff_nil in H1.
       rewrite H1.
       reflexivity.
      +destruct (S n mod 32 =? 0).
       {
         simpl in H0.
         Search (_ = _ \/ _).
         admit.
       }
       discriminate.
   }
   apply H0 in H.
   rewrite H.
   reflexivity.
Admitted.


Lemma encode_decode_flux_decoup : forall (lb : list bool) (l : list instruction),
    encode_flux_b l = Some lb -> decode_flux lb = Some l.
Proof.
  intros.
  unfold encode_flux_b in H.
  destruct encode_flux eqn:H1.
  -Search (encode_flux).
   apply encode_decode_decoup_flux_decoup in H1.
   unfold decode_flux.
   inversion H.
   rewrite H2.
   apply concat_listes_cut32 in H2.
   rewrite H2.
   simpl.
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

   
  
    
 



  
   
   

