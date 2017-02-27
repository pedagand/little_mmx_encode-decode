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



(* Lemma forall_tabP_cheat : forall (P : tag -> Prop) (p : tag -> bool) (t : tag), *)
(*     reflect (P t) (p t) -> reflect (P t) (forall_tag p). *)
(* Proof. *)
(*   intros P p t. *)
(*   intros H. *)
(*   Search reflect. *)
(*   apply reflect_iff in H. *)
(*   apply iff_reflect. *)
(*   rewrite H. *)
(*   apply iff_to_and. *)
(*   split. *)
(*   -intros H1. *)
(*    unfold forall_tag. *)
   
(*   unfold forall_tag. *)
  
(*   assert (xd : P t <-> p t = true -> reflect (P t) (forall_tag p)). *)
(*   { *)
(*     intros H. *)
(*     apply iff_reflect. *)
(*     apply iff_to_and. *)
(*     split. *)
(*     -apply iff_to_and in H. *)
(*   } *)
    
(*   assert (need : P t <-> p t = true -> reflect (P t) (p t)). *)
(*   { *)
(*     intros H. *)
(*     apply iff_reflect. exact H. *)
    
(*   } *)
(*   intros H. *)
(*   apply need in H. *)
(*   destruct (p t). *)
(*   -intros H. inversion H. *)
   
   
(*    apply iff_reflect. *)
(*    apply iff_to_and. *)
(*    split. *)
(*    +admit. *)
(*    +intros H'. exact H0. *)
(*   -intros H. inversion H. *)
(*    apply iff_reflect. *)
(*    split. *)
(*    +intros. *)
(*     auto. *)
(*    + *)
(*   assert (I : forall (b : bool), reflect (P t) (p t) = (P t) <-> b = true). *)
(*   { *)
(*     apply iff_reflect. *)
(*   } *)
(*   apply iff_reflect. *)
(*   apply iff_to_and. *)
(*   split. *)
(*   - *)


(* Lemma andLol : reflect True true. *)
(* Proof. *)
(*   Check ReflectT False. *)
(*   exact (ReflectT True I). *)
(* Qed. *)
(* (* Lemma andP : forall b1 b2 B1 B2,reflect (B1 /\ B2) (b1 && b2). *) *)
(* (* Proof. *) *)
(* (*   intros b1 b2 B1 B2. *) *)
(* (*   case b1; case b2. *) *)
(* (*   -simpl. constructor. *) *)
  
(* Lemma forall_tagP: forall (P : tag -> Prop)(p : tag -> bool), *)
(*     (forall (t : tag), reflect (P t) (p t)) -> *)
(*     reflect (forall t, P t) (forall_tag p). *)
(* Proof. *)
  
(*   Search reflect. *)
(*   intros P p H. (* reflect_iff *) *)
(*   Set Printing All. *)
(*   apply reflect_iff in H. *)
  
(*   apply iff_reflect.   *)
(*   apply iff_to_and. *)
(*   split. *)
(*   - *)
  

(* (* the first nat is the maximum we wan't to have in this bounded nat interval *) *)
(* Definition forall_bounded : nat -> (nat -> bool) -> bool. *)
(* Admitted. *)

(* Lemma forall_finP: forall (P : nat -> Prop)(p : nat -> bool) k, *)
(*     (forall t, reflect (P t) (p t)) -> *)
(*     reflect (forall n, n < k -> P n) (forall_bounded k p). *)
(* Admitted. *)

(* Definition imply (a b : bool): bool := if a then b else true. *)

(* Lemma implyP: forall A B a b, reflect A a -> reflect B b -> reflect (A -> B) (imply a b). *)
(* Admitted. *)

(* (* Lemma eq_natP: forall a b: nat, reflect (a = b) (eqdec a b). *) *)

(* (* Lemma eq_optionP: forall A a b: option A, (eq : A -> A -> bool) ->  reflect (a = b) (eqdec eq a b). *) *)

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

