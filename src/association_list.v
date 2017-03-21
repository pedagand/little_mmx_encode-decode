Require Import List Nat Arith. 
Import ListNotations.
Require Import Mmx.ast_instructions.

Check (1,2).
Check pair nat nat.
Definition tag_opcode_assoc :=
  list (tag * nat).

Scheme Equality for list.
Check list_beq.






(* actually this is a good name for this function :p *)
Fixpoint lookup (t : tag) (l : tag_opcode_assoc) : option nat :=
  match l with
    | [] => None
    | (t',n) :: tl => if tag_beq t t'
                      then Some n
                      else lookup t tl
  end.
(* actually this is a good name for this function :p *)
Fixpoint lookdown (n : nat) (l : tag_opcode_assoc) : option tag :=
  match l with
    | [] => None
    | (t,n') :: tl => if  eqb n n'
                      then Some t
                      else lookdown n tl
  end.

(* this table is an association list of type tag_opcode_assoc with every associations that can be made in our langage *)
Definition encdec : tag_opcode_assoc := [(tag_n(ADD),0);(tag_n(AND),1);(tag_i(ADD_I),2);(tag_i(AND_I),3)].

Theorem lookup_encdec : forall (t : tag), exists n,
                          lookup t encdec = Some n.
Proof.
  destruct t.
  -destruct t.
   +simpl. exists 0. reflexivity.
   +simpl. exists 1. reflexivity.
  -destruct t.
   +simpl. exists 2. reflexivity.
   +simpl. exists 3. reflexivity.
Qed.


Require Import Bool.

Print tag.

Definition forall_tag_n (p : tag_normal -> bool): bool :=
  andb (p ADD) (p AND).

Definition forall_tag_i (p : tag_immediate -> bool): bool :=
  andb (p ADD_I) (p AND_I).

Definition forall_tag (p : tag -> bool): bool :=
  andb (forall_tag_n (fun (x : tag_normal) => p (tag_n x)))
       (forall_tag_i (fun (x : tag_immediate) => p (tag_i x))).


Print reflect.

Definition propP := forall x : nat, x = x.
Check propP.

Lemma test_reflect : True -> reflect True true.
Proof.
  exact (ReflectT True).
Qed.




Lemma helpBefore1 : forall (f : tag -> bool), forall_tag f = true -> (forall (t: tag), f t = true).
Proof.  
  intros f.
  unfold forall_tag.
  intros H.
  Search (_ && _ = true).
  apply andb_prop in H.
  unfold forall_tag_n in H.
  unfold forall_tag_i in H.
  destruct H.  
  apply andb_prop in H.
  destruct H.
  apply andb_prop in H0.
  destruct H0.
  destruct t.
  {
    -destruct t.
     +rewrite H.
      reflexivity.
     +rewrite H1.
      reflexivity.
  }
  {
     -destruct t.
      +rewrite H0.
       reflexivity.
      +rewrite H2.
       reflexivity.
   }
Qed.

Lemma helpBefore2 : forall (f : tag -> bool), (forall (t: tag), f t = true) -> forall_tag f = true.
Proof.
  intros f H.
  unfold forall_tag.
  Search (_ && _ = true).
  apply andb_true_intro.
  split.
  -compute. rewrite H. rewrite H. reflexivity.
  -compute. rewrite H. rewrite H. reflexivity.
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
   rewrite helpBefore2.
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
   rewrite helpBefore1 in H.
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

Check forall_bounded.
(* (* SAVE THIS *) *)
(* Lemma help_forall_findP1 : forall (f : nat -> bool), (forall (n: nat), f n = true) -> forall (k : nat), forall_bounded k f = true. *)
(* Proof. *)
(*   intros. *)
(*   induction k. *)
(*   -simpl. *)
(*    apply H. *)
(*   -simpl. *)
(*    rewrite IHk. *)
(*    Search (_ && _ = true). *)
(*    apply andb_true_intro. *)
(*    split. *)
(*    +apply H. *)
(*    +reflexivity. *)
(* Qed. *)
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
      
      admit.
    }
    {
      Search (S _ <= S _).
      apply le_S_n in H1.
      exact H1.
    }
Admitted.
    
    

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


Definition eq_mnat (t1 t2: option nat): bool :=
  match t1,t2 with
  | Some n1,Some n2 => beq_nat n1 n2
  | _,_ => false
  end.

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
  

Definition lookdown_encdecP : bool :=
  forall_bounded 3 (fun n =>                     
                      forall_tag (fun t => imply (eq_mtag (lookdown n encdec) (Some t))
                                                 (eq_mnat (lookup t encdec) (Some n)))).

Lemma lookdown_n_inf_3 : forall (n : nat) (t : tag), lookdown n encdec = Some t -> n <=3.
Proof.
  destruct n.
  -intros.
   Search (0 <= _).
   apply Peano.le_0_n.
  -{destruct n.    
    -intros.      
     Search (S _ <= S _).
     apply le_n_S.
     apply Peano.le_0_n.
    -{
        destruct n.
        -intros.
         repeat (apply le_n_S).
         apply Peano.le_0_n.
        -{
            destruct n.
            -intros.
             repeat (apply le_n_S).
             apply Peano.le_0_n.
            -discriminate.
          }
      }
   }
Qed.



Lemma lookdown_encdecP_implies : lookdown_encdecP = true -> forall (n : nat) (t : tag), n <= 3 -> lookdown n encdec = Some t.
Proof.
Admitted.

Lemma lookdown_equiv : forall (n : nat) (t : tag), n <= 3 <-> lookdown n encdec = Some t.
  Admitted.
(*
Theorem lookdown_encdec : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n.
Proof.
  intros n.
  assert (reflect (forall (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n) (forall_tag lookdown_encdecP)).
  {
    Search reflect.
    Check forall_tagP.
    apply forall_tagP.
    intros t.
    apply iff_reflect.
    apply iff_to_and.
    split.
    -intros.
     induction t.
    +{
        induction t.
        -reflexivity.
        -reflexivity.        
      }
    +{
        induction t.
        -reflexivity.
        -reflexivity.
      }
    -admit.
     
  }
  assert (H': forall_tag lookdown_encdecP = true) by reflexivity.
  rewrite H' in H.
  inversion H. auto.
Admitted.
*)

Theorem lookdup_encdec : forall (t : tag) (n : nat), lookup t encdec = Some n -> lookdown n encdec = Some t.
Proof.
Admitted.


Theorem lookdown_encdec' : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n.
Proof.
  SearchAbout (_ < _ \/ _).
  (* Nat.lt_ge_cases" *)
  assert (reflect (forall (n : nat), n <= 3 -> forall
                       (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n)
                  lookdown_encdecP).
  {
    unfold lookdown_encdecP.
    SearchAbout forall_bounded. 
    apply forall_finP.        
    intro n.
    Check forall_tag.
    apply forall_tagP.
    SearchAbout imply.
    intros t.
    apply implyP.
    -assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
    {
      apply iff_reflect.
      apply iff_to_and.
      split.
      +intros.
       rewrite H.
       simpl.
       rewrite tag_beq_reflexivity.
       reflexivity.
      +intros.
       apply eq_mtag_equiv in H.
       exact H.       
    }
    exact H.
    -assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
    {
      apply iff_reflect.
      apply iff_to_and.
      split.
      -intros.
      rewrite H.
      simpl.
      Search (_ =? _).
      rewrite <- beq_nat_refl.
      reflexivity.
      -intros.
       apply eq_mnat_equiv in H.
       exact H.
    }
    exact H.
  }
  
  assert (H': lookdown_encdecP = true) by reflexivity.
  rewrite H' in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n 3).
  intros.
  destruct H1.
  -apply H0.
   exact H1.
   exact H2.
  -assert (exists m, n = 4 + m).
   {
     admit.
   }
   destruct H3.
   subst n.
   simpl in H2.
   discriminate.
  Admitted.
