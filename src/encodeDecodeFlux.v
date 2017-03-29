Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encodeProof Mmx.decodeProof Mmx.encode.



(* First i need some lemma about the cut32 comportement *)
Lemma cut32_size : forall (n : nat) (l : list bool) (res : (list (list bool))),
    cut32 l = Some res -> length res = (length l) / 32.
Proof.
Admitted.   


(* size of encode_flux l = Some lb *)
Lemma encode_flux_size : forall (l : list instruction) (lb : list bool),
    encode_flux l = Some lb -> (length lb) mod 32 = 0.
  Admitted.




Lemma encode_decode_fold : forall (li : list instruction) (lbi : list binary_instruction),
    encode_flux_lbi li = Some lbi -> decode_fold lbi = Some li.
Proof.
  Search fold_right.    
  induction li.
  -intros.
   simpl in H.
   inversion H.
   reflexivity.
  -intros.
   assert (keep : encode_flux_lbi (a :: li) = Some lbi) by auto.
   unfold encode_flux_lbi in H.
   simpl in H.
   unfold encode_flux_lbi in IHli.
(*    unfold fold_function_encode in H. *)
   apply bind_rewrite in H.
   destruct H.
   destruct H.
   destruct li.
   +simpl in H.
    inversion H.
    apply commut_equal in H0.
    Search encode.
    apply encode_decode in H0.
    unfold decode_fold.
    simpl.
    unfold fold_function_decode.
    rewrite H0.
    reflexivity.
   +Search fold_right.
    Check fold_left_rev_right.
    unfold encode_flux_lbi in keep.


   assert(fold_function_encode a (fold_right fold_function_encode (Some []) li) = Some lbi -> Some (x :: li) = Some lbi).

   destruct li.
   +simpl in H.
    inversion H.
    apply commut_equal in H0.
    Search encode.
    apply encode_decode in H0.
    unfold decode_fold.
    simpl.
    unfold fold_function_decode.
    rewrite H0.
    reflexivity.
   +unfold encode_flux_lbi in keep.    
    destruct (fold_right fold_function_encode (Some []) (i :: li)).
    {      
      inversion H.
      simpl.
      unfold decode_fold.
      
    }


     assert encode a = Some x -> (fold_right fold_function_encode (Some []) (i :: li)

  (fun (i : instruction) (lbi : option (list binary_instruction)) =>
           bind (encode i) (fun bi : binary_instruction => match lbi with
                                                           | Some l => Some (bi :: l)
                                                           | None => None
                                                           end)) (Some []) (i :: li) 

     
   destruct (encode i) in H.
   assert (fold_function_encode a (fold_right fold_function_encode (Some []) li) = Some lbi ->
           
   specialize (IHli lbi).
   unfold encode_flux_lbi in IHli.
   
Admitted.



(* these are the final lemma we wan't *)
Lemma encode_decode_flux : forall (l : list instruction) (lb : list bool),
    encode_flux l = Some lb -> decode_flux lb = Some l.
Proof.
  intros.
  assert (keep : encode_flux l = Some lb) by auto.
  unfold encode_flux in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  SearchAbout (_ = _).
  apply commut_equal in H0.
  apply encode_decode_fold in H0.
  unfold decode_flux.
  apply encode_flux_size in keep.
  unfold cut32.
  rewrite keep.
  unfold decode_fold in H0.
  simpl.
  
   
   
