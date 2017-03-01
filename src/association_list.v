Require Import List Nat. 
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

Lemma help_forall_findP1 : forall (f : nat -> bool), (forall (n: nat), f n = true) -> forall (k : nat), forall_bounded k f = true.
Proof.
  intros.
  induction k.
  -simpl.
   apply H.
  -simpl.
   rewrite IHk.
   Search (_ && _ = true).
   apply andb_true_intro.
   split.
   +apply H.
   +reflexivity.
Qed.
            
  
  

Lemma forall_finP: forall (P : nat -> Prop)(f : nat -> bool) (k : nat),
    (forall (n : nat), reflect (P n) (f n)) ->
    reflect (forall n, n < k -> P n) (forall_bounded k f).
Proof.
  intros P f k H.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -intros.
   assert ( -> forall_bounded k f = true)
  
  
  

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

(* Lemma eq_natP: forall a b: nat, reflect (a = b) (eqdec a b). *)

(* Lemma eq_optionP: forall A a b: option A, (eq : A -> A -> bool) ->  reflect (a = b) (eqdec eq a b). *)
 
(* (* TODO : i know that i can refoctor this proof but at the first try i didn't succeed so will try later *) *)
(* Theorem look_up_down_encdec : forall (n : nat) (t : tag), *)
(*                                 lookup t encdec = Some n -> lookdown n encdec = Some t. *)
(* Proof. *)
(* intros. *)
(* repeat match goal with *)
(*        | t : tag |- _ => destruct t *)
(*        | t : tag_normal |- _ => destruct t *)
(*        | t : tag_immediate |- _ => destruct t *)
(*        end; inversion H; auto. *)
(* Qed. *)

(* (* uglyest proof in the world *) *)
(* Theorem look_down_up_encdec : forall (n : nat) (t : tag), *)
(*                                 lookdown n encdec = Some t -> lookup t encdec = Some n. *)
(* Proof. *)
(*   induction n. *)
(*   -intros t H. *)
(*    simpl in H. *)
(*    inversion H. *)
(*    reflexivity. *)
(*   -{induction n. *)
(*     -intros t H. *)
(*      simpl in H. *)
(*      inversion H. *)
(*      reflexivity. *)
(*     -{induction n. *)
(*       -intros t H. *)
(*        simpl in H. *)
(*        inversion H. *)
(*        reflexivity. *)
(*       -{induction n. *)
(*       -intros t H. *)
(*        simpl in H. *)
(*        inversion H. *)
(*        reflexivity. *)
(*       -assert(help : forall (n' : nat), lookdown (S (S (S (S n')))) encdec = None). *)
(*        { *)
(*          induction n'. *)
(*          -reflexivity. *)
(*          -reflexivity. *)
(*        } *)
(*        intros t H. *)
(*        rewrite help in H. *)
(*        discriminate. *)
(*        } *)
(*      } *)
(*    } *)
(* Qed. *)


(* (* (* if i wan't it's very easy to proof with forall t exists n but this theorem is better and actually it's true *) *) *)
(* (* Theorem look_down_up_encdec : forall (n : nat) (t : tag), *) *)
(* (*                                 lookdown n encdec = Some t -> lookup t encdec = Some n. *) *)
(* (* Proof. *) *)
(* (*   assert (I : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n). *) *)
(* (*   { *) *)
(* (*     induction n. *) *)
(* (*     -intros t H. *) *)
(* (*      simpl in H. *) *)
(* (*      discriminate. *) *)
(* (*     - *) *)
      

    
(* (*     induction encdec as [|t' tl IHencdec].     *) *)
(* (*     -assert (I_1 : forall (t : tag) (n : nat), lookdown n [] = Some t -> lookup t [] = Some n). *) *)
(* (*      { *) *)
(* (*        simpl. *) *)
(* (*        intros t n H. *) *)
(* (*        discriminate. *) *)
(* (*      } *) *)
(* (*      exact I_1. *) *)
(* (*     -assert (I_2 : forall (t : tag) (n : nat), lookdown n (t' :: tl) = Some t -> lookup t (t' :: tl) = Some n). *) *)
(* (*      { *) *)
       




       
(* (*        intros t0 n. *) *)
(* (*        destruct a. *) *)
(* (*        -unfold lookdown. *) *)
(* (*         destruct (n =? n0). *) *)
(* (*         +intro H. *) *)
(* (*          inversion H. *) *)
(* (*          rewrite <- H1. *) *)
(* (*          assert (I_2_1 : forall (t' : tag) (n' : nat) (tl : list (tag * nat)), lookup t' ((t', n') :: tl) = Some n'). *) *)
(* (*          { *) *)
(* (*            intros t' n' tl. *) *)
(* (*            unfold lookup. *) *)
(* (*            assert (I_2_1_1 : forall (t'' : tag), tag_beq t'' t'' = true). *) *)
(* (*            { *) *)
(* (*              destruct t''. *) *)
(* (*              -destruct t2. *) *)
(* (*               +reflexivity. *) *)
(* (*               +reflexivity. *) *)
(* (*              -destruct t2. *) *)
(* (*               +reflexivity. *) *)
(* (*               +reflexivity.                 *) *)
(* (*            } *) *)
(* (*            rewrite I_2_1_1. *) *)
(* (*            reflexivity. *) *)
(* (*          } *) *)
(* (*          rewrite <- IHt. *) *)
(* (*      } *) *)
        
     
(* (*   } *) *)
  
(* (* Admitted. *) *)

