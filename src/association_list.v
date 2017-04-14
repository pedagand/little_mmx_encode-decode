Require Import List Nat Arith Bool.  
Import ListNotations.
Require Import Mmx.ast_instructions.


Check (1,2).
Check pair nat nat.
Definition tag_opcode_assoc :=
  list (tag * instructionStructure * nat).

Scheme Equality for list.
Check list_beq.






(* actually this is a good name for this function :p *)
(* finally i need both to ensure that lookup lookdown will have the same result *)
Fixpoint lookup (t : tag) (i : instructionStructure) (l : tag_opcode_assoc) : option (nat*instructionStructure) :=
  match l with
    | [] => None
    | (t',i',n) :: tl => if tag_beq t t' && instructionStructure_beq i i'
                      then Some (n,i') 
                      else lookup t i tl
  end.
(* actually this is a good name for this function :p *)
(* now i need a couple with (instructionStructure * tag) to decode the instruction *)
Fixpoint lookdown (n : nat) (l : tag_opcode_assoc) : option (tag * instructionStructure) :=
  match l with
    | [] => None
    | (t,m,n') :: tl => if  beq_nat n n'
                      then Some (t,m)
                      else lookdown n tl
  end.

(* this table is an association list of type tag_opcode_assoc with every associations that can be made in our langage *)
Definition encdec : tag_opcode_assoc := 
  [
    (tag_t(ADD NORMAL),is_t RRR,0);
      (tag_t(ADD NORMAL),is_t RRI,1);
      (tag_t(ADD UNSIGNED),is_t RRR,2);
      (tag_t(ADD UNSIGNED),is_t RRI,3);
      (tag_t(ADD FLOAT),is_t RRR,4);
      (tag_t(ADD FLOAT),is_t RRI,5);
      
      (tag_t(SUB NORMAL),is_t RRR,6);
      (tag_t(SUB NORMAL),is_t RRI,7);
      (tag_t(SUB UNSIGNED),is_t RRR,8);
      (tag_t(SUB UNSIGNED),is_t RRI,9);
      (tag_t(SUB FLOAT),is_t RRR,10);
      (tag_t(SUB FLOAT),is_t RRI,11);

      (tag_t(MUL NORMAL),is_t RRR,12);
      (tag_t(MUL NORMAL),is_t RRI,13);
      (tag_t(MUL UNSIGNED),is_t RRR,14);
      (tag_t(MUL UNSIGNED),is_t RRI,15);
      (tag_t(MUL FLOAT),is_t RRR,16);
      (tag_t(MUL FLOAT),is_t RRI,17);

      (tag_t(DIV NORMAL),is_t RRR,18);
      (tag_t(DIV NORMAL),is_t RRI,19);
      (tag_t(DIV UNSIGNED),is_t RRR,20);
      (tag_t(DIV UNSIGNED),is_t RRI,21);
      (tag_t(DIV FLOAT),is_t RRR,22);
      (tag_t(DIV FLOAT),is_t RRI,23);

      (tag_t(BIDON),is_t RRR,24);
      (tag_t(BIDON),is_t RRI,25);

      (tag_d(BZ),is_d RR,26);
      (tag_d(BIDON_DUO),is_d RR,27);

      (tag_u(BIDON_UNO2),is_u I,28);
      (tag_u(BIDON_UNO),is_u I,29)
  ].
     


Definition forall_tag_ter (p : tag_ter -> bool) : bool :=
 p(ADD NORMAL) && 
  p(ADD NORMAL) &&
  p(ADD UNSIGNED) &&
  p(ADD UNSIGNED) &&
  p(ADD FLOAT) &&
  p(ADD FLOAT) &&
  p(SUB NORMAL) &&
  p(SUB NORMAL) &&
  p(SUB UNSIGNED) &&
  p(SUB UNSIGNED) &&
  p(SUB FLOAT) &&
  p(SUB FLOAT) &&
  p(MUL NORMAL) &&
  p(MUL NORMAL) &&
  p(MUL UNSIGNED) &&
  p(MUL UNSIGNED) &&
  p(MUL FLOAT) &&
  p(MUL FLOAT) &&
  p(DIV NORMAL) &&
  p(DIV NORMAL) &&
  p(DIV UNSIGNED) &&
  p(DIV UNSIGNED) &&
  p(DIV FLOAT) &&
  p(DIV FLOAT) &&
  p(BIDON) &&
  p(BIDON).

Definition forall_tag_duo (p : tag_duo -> bool) : bool :=
  p BZ && 
    p BIDON_DUO.

Definition forall_tag_uno (p : tag_uno -> bool) : bool :=
  p BIDON_UNO2 && p BIDON_UNO.
  




Definition forall_tag (p : tag -> bool): bool :=
  (forall_tag_ter (fun x => p (tag_t x))) &&
                                            (forall_tag_duo (fun x => p (tag_d x))) &&
                                            (forall_tag_uno (fun x => p (tag_u x))).


Definition propP := forall x : nat, x = x.
Check propP.

Lemma test_reflect : True -> reflect True true.
Proof.
  exact (ReflectT True).
Qed.



(* previously helpBefore1 *)
Lemma help_forall_tagP1 : forall (f : tag -> bool), forall_tag f = true -> (forall (t: tag), f t = true).
Proof.
  intros f.
  unfold forall_tag.
  intros H.  
  repeat (apply andb_prop in H; destruct H).
  repeat (apply andb_prop in H1; destruct H1).
  repeat (apply andb_prop in H0; destruct H0).
  repeat destruct t; try destruct t; (try destruct a; auto); auto.
Qed.

(* previously helpBefore2 *)
Lemma help_forall_tagP2 : forall (f : tag -> bool), (forall (t: tag), f t = true) -> forall_tag f = true.
Proof.
  intros f H.
  unfold forall_tag.
  Search (_ && _).
  Search (_ && _ = true).
  repeat (apply andb_true_intro ; split ; auto).
Qed.


Lemma forall_tagP: forall (P : tag -> Prop)(f : tag -> bool),
    (forall (t : tag), reflect (P t) (f t)) ->
    reflect (forall t, P t) (forall_tag f).
Proof.
  intros P f H.
  Search reflect.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -Search forall_tag.
   intros.
   Check help_forall_tagP2.
   rewrite help_forall_tagP2.
   +reflexivity.
   +intros t.
    specialize (H t).
    Search forall_tag.
    apply reflect_iff in H.
    inversion H.
    specialize (H0 t).
    apply H1.
    exact H0.
    (* this part is ok !!! ;) *)
  -intros.
   specialize (H t).
   rewrite help_forall_tagP1 in H.
   inversion H.
   +exact H1.
   +exact H0.
Qed.


    
SearchAbout leb.
(* the first nat is the maximum we wan't to have in this bounded nat interval *)
Fixpoint forall_bounded (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => f 0
  | S n => f (S n) && forall_bounded n f
  end.

Lemma help_forall_findP1 : forall (f : nat -> bool) (k : nat), (forall (n: nat), n <= k -> f n = true) -> forall_bounded k f = true.
Proof.
  intros.
  induction k.
  -apply H.
   reflexivity.
  -simpl.
   Search (_ && _ = true).
   apply andb_true_intro.
   split.
   +apply H.
    reflexivity.
   +apply IHk.
    intros n.
    specialize (H n).
    intros.
    apply H.
    Search (_ <= S _).
    apply le_S in H0.
    exact H0.
Qed.

Lemma help_forall_findP2 :
  forall (k : nat) (f : nat -> bool), forall_bounded k f = true -> (forall (n: nat), n <= k -> f n = true).
Proof.
  induction k.
  -simpl.
   intros.
   Search (_ <= 0).
   apply le_n_0_eq in H0.
   rewrite <- H0.
   exact H.
  -destruct n.
   +intros.
    apply IHk.
    simpl in H.
    Search (_ && _ = true).
    apply andb_prop in H.
    destruct H.
    exact H1.
    apply Peano.le_0_n.
   +apply andb_prop in H. 
    fold forall_bounded in H.
    destruct H.
    intros.
    change (f (S n) = true) with ((fun n => f (S n)) n = true).
    apply IHk.
    {(* c'est donner par H0 et H mais faut trouver un théoreme pour reussir a exprimer ça *)
      assert (forall (k' : nat) (f' : nat -> bool) , f' (S k') = true -> forall_bounded k' f' = true -> forall_bounded k' (fun n0 : nat => f' (S n0)) = true).
      {
        induction k'.
        -intros.
         simpl.
         auto.
        -intros.
         simpl.
         rewrite H2.
         simpl.
         apply IHk'.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
      }
      auto.       
    }
    {
      Search (S _ <= S _).
      apply le_S_n in H1.
      exact H1.
    }
Qed.
        
Lemma forall_finP: forall (P : nat -> Prop)(f : nat -> bool) (k : nat),
    (forall (n : nat), reflect (P n) (f n)) ->
    reflect (forall n, n <= k -> P n) (forall_bounded k f).
Proof.
  intros P f k H.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -intros.
   Check help_forall_findP1.
   apply help_forall_findP1.
   intros.
   specialize (H n).
   apply reflect_iff in H.
   inversion H.
   apply H2.
   apply H0.
   exact H1.
  -intros.
   Check help_forall_findP2.
   eapply help_forall_findP2 in H0.
   specialize (H n).
   rewrite H0 in H.
   inversion H.
   exact H2.
   exact H1.
Qed.

Definition forall_instructionStructure_t (f : instructionStructure_t -> bool) : bool :=
  f RRR && f RRI && f RIR && f IRR && f RII && f III && f IRI.
Definition forall_instructionStructure_d (f : instructionStructure_d -> bool) : bool :=
  f RR && f RI && f IR && f II.
Definition forall_instructionStructure_u (f : instructionStructure_u -> bool) : bool :=
  f I && f R.
Definition forall_instructionStructure (f : instructionStructure -> bool) : bool :=
  (forall_instructionStructure_t (fun x => f (is_t x))) &&
                                                        (forall_instructionStructure_d (fun x => f (is_d x))) && 
                                                        (forall_instructionStructure_u (fun x => f (is_u x))).



Lemma help_forall_instructionStructureP1: forall (f : instructionStructure -> bool),
    forall_instructionStructure f = true -> (forall (i : instructionStructure), f i = true).
Proof.
  intros f H. 
  unfold forall_instructionStructure in H.
  repeat (apply andb_prop in H; destruct H).
  repeat (apply andb_prop in H1; destruct H1).
  repeat (apply andb_prop in H0; destruct H0).
  repeat (destruct i; destruct i; auto).
Qed.

(* previously helpBefore2 *)
Lemma help_forall_instructionStructureP2 : forall (f : instructionStructure -> bool),
    (forall (i: instructionStructure),
        f i = true) -> forall_instructionStructure f = true.
Proof.
  intros f H.
  unfold forall_instructionStructure.
  Check andb_true_intro.
  repeat (apply andb_true_intro ; split ; auto).
Qed.


Lemma forall_instructionStructureP: forall (P : instructionStructure -> Prop)(f : instructionStructure -> bool),
    (forall (i : instructionStructure), reflect (P i) (f i)) ->
    reflect (forall i, P i) (forall_instructionStructure f).
Proof.
  intros.
  Search reflect.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -intros.
   Check help_forall_instructionStructureP1.
   Check help_forall_instructionStructureP2.
   apply help_forall_instructionStructureP2.
   Search (reflect).
   intros i.
   specialize (H i).
   apply reflect_iff in H.
   destruct H.
   apply H.
   specialize (H0 i).
   auto.
  -intros.
   specialize (H i).
   Search forall_instructionStructure.
   Check help_forall_instructionStructureP1.
   eapply help_forall_instructionStructureP1 in H0.
   rewrite H0 in H.
   inversion H.
   auto.
Qed.
  

Definition imply (a b : bool): bool := if a then b else true.

Lemma implyP: forall A B a b, reflect A a -> reflect B b -> reflect (A -> B) (imply a b).
Proof.
  intros.
  apply reflect_iff in H.
  inversion H.
  apply reflect_iff in H0.
  inversion H0.
  apply iff_reflect.
  apply iff_to_and.
  unfold imply.
  split.  
  -intros.
   destruct a.
   +apply H3.
    apply H5.
    apply H2.
    reflexivity.
   +reflexivity. 
  -intros.
   destruct b.
   +apply H4.
    reflexivity.
   +destruct a.
    {
      discriminate.
    }
    {
      apply H4.
      apply H1.
      exact H6.
    }
Qed.

SearchAbout beq_nat.

Definition eq_mtag (t1 t2: option tag): bool :=
  match t1,t2 with
  | Some t1', Some t2' => tag_beq t1' t2'
  | _,_ => false
  end.

Definition eq_mtag_is (t_is1 t_is2 : option (tag * instructionStructure)) : bool :=
  match t_is1,t_is2 with
  | Some (t1,is1), Some (t2,is2) => tag_beq t1 t2 && instructionStructure_beq is1 is2
  | _,_ => false
  end.

Lemma eq_mtag_equiv : forall (t1 t2 : option tag), eq_mtag t1 t2 = true -> t1 = t2.
Proof.
  destruct t1.
  -destruct t2.
   +simpl.
   intros.
   apply tag_beq_different in H.
   rewrite H.
   reflexivity.
   +discriminate.
  -discriminate.
Qed.

Lemma eq_mtag_is_equiv : forall (t1 t2 : option (tag * instructionStructure)), eq_mtag_is t1 t2 = true -> t1 = t2.
Proof.
  Admitted.

Definition eq_mnat (n1 n2: option nat): bool :=
  match n1,n2 with
  | Some n1',Some n2' => beq_nat n1' n2'
  | _,_ => false
  end.

Definition eq_mnat_is (n_is1 n_is2: option (nat*instructionStructure)): bool :=
  match n_is1,n_is2 with
  | Some (n1,is1),Some (n2,is2) => beq_nat n1 n2 && instructionStructure_beq is1 is2
  | _,_ => false
  end.

Lemma eq_mnat_is_equiv : forall (n_is1 n_is2 : option (nat*instructionStructure)), eq_mnat_is n_is1 n_is2 = true -> n_is1 = n_is2.
Proof.
  destruct n_is1.
  -destruct n_is2.
   +simpl.
    intros.
    destruct p eqn:H0.
    destruct p0 eqn:H1.
    Search (_ && _ = true).
    apply andb_true_iff in H.
    destruct H.
    apply beq_nat_true in H.
    Search instructionStructure_beq.
    apply instructionStructure_beq_different in H2.
    rewrite H.
    rewrite H2.
    reflexivity.
   +intros.
    simpl in H.
    destruct p.
    discriminate.
  -intros.
   simpl in H.
   discriminate.
Qed.

Lemma eq_mnat_equiv : forall (n1 n2 : option nat), eq_mnat n1 n2 = true -> n1 = n2.
Proof.
  destruct n1.
  -destruct n2.
   +simpl.
    intros.
    Search (_ =? _ = true).
    apply beq_nat_true in H.
    rewrite H.
    reflexivity.
   +discriminate.
  -discriminate.
Qed.



Definition lookdown_encdec : bool :=
  forall_bounded 29 (fun n =>                     
                       forall_tag (fun t =>
                                     forall_instructionStructure (fun i => imply (eq_mtag_is (lookdown n encdec) (Some (t,i)))
                                                                                  (eq_mnat_is (lookup t i encdec) (Some (n,i)))))).
Definition lookup_encdec : bool :=
  forall_bounded 29 (fun n =>                     
                       forall_tag (fun t =>
                                     forall_instructionStructure (fun i =>  imply (eq_mnat_is (lookup t i encdec) (Some (n,i)))
                                                                                  (eq_mtag_is (lookdown n encdec) (Some (t,i)))))).
(* Some (tag_t (SUB FLOAT), is_t RRR) *)
Definition testlookup := match lookdown 1 encdec with
                         | Some (t,i) => lookup t i encdec
                         | None => None
                         end.                                     
Compute testlookup.

Lemma lookdown_encdec_true : lookdown_encdec = true.
Proof. vm_compute; reflexivity. Qed.

Lemma lookup_encdec_true : lookup_encdec = true.
Proof. vm_compute; reflexivity. Qed.

Lemma lookdown_encdecP: 
  reflect (forall (n : nat), n <= 29 ->
            forall (t : tag) (i : instructionStructure),
              lookdown n encdec = Some (t,i) ->
              lookup t i encdec = Some (n,i))
          lookdown_encdec.
Proof.
  unfold lookdown_encdec.
  Check forall_finP.
  apply forall_finP.
  intros n.
  apply forall_tagP.
  intros t.
  apply forall_instructionStructureP.
  intros i.
  apply implyP.
  -assert(reflect (lookdown n encdec = Some (t, i)) (eq_mtag_is (lookdown n encdec) (Some (t, i)))).
   {
     apply iff_reflect.
     apply iff_to_and.
     split.
     +intros.
      rewrite H.
      simpl.
      rewrite tag_beq_reflexivity.
      rewrite instructionStructure_beq_reflexivity.      
      reflexivity.
     +intros.
      Check eq_mtag_equiv.
      Search eq_mtag_is.
      apply eq_mtag_is_equiv in H.
      auto.
   }
   auto.
  -assert(reflect (lookup t i encdec = Some (n, i)) (eq_mnat_is (lookup t i encdec) (Some (n, i)))).
   {
     apply iff_reflect.
     apply iff_to_and.
     split.
     -intros.
      rewrite H.
      simpl.
      Search (_ =? _).
      rewrite <- beq_nat_refl.
      rewrite instructionStructure_beq_reflexivity.
      reflexivity.
     -intros.
      Search eq_mnat_is.
      apply eq_mnat_is_equiv in H.
      exact H.
   }
   auto.
Qed.



  


Theorem lookdown_lookup : forall (n : nat) (i : instructionStructure) (t : tag), lookdown n encdec = Some (t,i) -> lookup t i encdec = Some (n,i).
Proof.
  (* i admit this only because computing is too long *)
  assert (H': lookdown_encdec = true) by apply lookdown_encdec_true.
  pose proof lookdown_encdecP.
  rewrite H' in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n 29).
  intros.
  destruct H1.
  -apply H0.
   exact H1.
   exact H2.
  -assert (exists m, n = 29 + m). {eexists. eapply le_plus_minus. Check le_plus_minus. eauto.
      by (eexists; eapply le_plus_minus; eauto).
   destruct H3.
   subst n.
   simpl in H2.
   discriminate.
Qed.


(* need to find how to refactor the proof *)
Lemma lookup_val : forall (t : tag), forall (n : nat), lookup t encdec = Some n -> n <= 226.
Proof.
Admitted.

Definition forall_inv (t: tag)(p: nat -> bool): bool.
Admitted.

Lemma forall_invP {P}{p}{t} : (forall n, reflect (P n) (p n)) ->
                           reflect (forall (n : nat), lookup t encdec = Some n -> P n)
                                   (forall_inv t p).
Admitted.

Lemma lookup_true : forall_tag (fun t =>
                       forall_inv t (fun n =>
                         n <=? 256)) = true.
Proof. try (vm_compute; reflexivity). Admitted.


Theorem lookup_encdecP:
  reflect (forall (n : nat), n <= 226 ->
             forall (t : tag),
               lookup t encdec = Some n ->
               lookdown n encdec = Some t)
          lookup_encdec.
Proof.
unfold lookdown_encdec.
SearchAbout reflect.
Check forall_finP.
apply forall_finP.
Check forall_tagP.
intros n.
apply forall_tagP.
SearchAbout reflect.
Check implyP.
intros t.
apply implyP.
-assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
 {
   apply iff_reflect.
   apply iff_to_and.
   split.
   +intros.
    rewrite H.
    simpl.
    apply Nat.eqb_refl.
   +intros.
    apply eq_mnat_equiv in H.
    exact H.
 }
 exact H.
    -assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
     {
       apply iff_reflect.
       apply iff_to_and.
       split.
       +intros.
        rewrite H.
        simpl.
        apply tag_beq_reflexivity.
       +intros.
        apply eq_mtag_equiv in H.
        exact H.
     }
     exact H.
Qed.

Theorem lookup_lookdown : forall (n : nat) (t : tag) , lookup t encdec = Some n -> lookdown n encdec = Some t.
Proof.
  (* same as previously *)
  pose proof lookup_encdecP.
  assert (lookup_encdec = true) by apply lookup_encdec_true.
  rewrite H0 in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n 226).
  intros.
  destruct H2.
  -apply H1.
   exact H2.
   exact H3.
  - pose proof lookup_val t n H3.
    now apply lt_not_le in H4.
Qed.



