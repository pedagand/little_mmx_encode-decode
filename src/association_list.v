Require Import List Nat. 
Import ListNotations.
Require Import ast_instructions.

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


(* TODO : i know that i can refoctor this proof but at the first try i didn't succeed so will try later *)
Theorem look_up_down_encdec : forall (n : nat) (t : tag),
                                lookup t encdec = Some n -> lookdown n encdec = Some t.
Proof.
  assert (I : forall (n : nat) (t : tag), lookup t encdec = Some n -> lookdown n encdec = Some t).
  {
    destruct t.
    -destruct t.
     +intros H.
      simpl in H.
      inversion H.
      reflexivity.
     +intros H.
      simpl in H.
      inversion H.
      reflexivity.
    -destruct t.
     +intros H.
      simpl in H.
      inversion H.
      reflexivity.
     +intros H.
      simpl in H.
      inversion H.
      reflexivity.
  }
  exact I.
Qed.
   
(* uglyest proof in the world *)
Theorem look_down_up_encdec : forall (n : nat) (t : tag),
                                lookdown n encdec = Some t -> lookup t encdec = Some n.
Proof.
  induction n.
  -intros t H.
   simpl in H.
   inversion H.
   reflexivity.
  -{induction n.
    -intros t H.
     simpl in H.
     inversion H.
     reflexivity.
    -{induction n.
      -intros t H.
       simpl in H.
       inversion H.
       reflexivity.
      -{induction n.
      -intros t H.
       simpl in H.
       inversion H.
       reflexivity.
      -assert(help : forall (n' : nat), lookdown (S (S (S (S n')))) encdec = None).
       {
         induction n'.
         -reflexivity.
         -reflexivity.
       }
       intros t H.       
       rewrite help in H.
       discriminate.
       }
     }
   }
Qed.


(* (* if i wan't it's very easy to proof with forall t exists n but this theorem is better and actually it's true *) *)
(* Theorem look_down_up_encdec : forall (n : nat) (t : tag), *)
(*                                 lookdown n encdec = Some t -> lookup t encdec = Some n. *)
(* Proof. *)
(*   assert (I : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n). *)
(*   { *)
(*     induction n. *)
(*     -intros t H. *)
(*      simpl in H. *)
(*      discriminate. *)
(*     - *)
      

    
(*     induction encdec as [|t' tl IHencdec].     *)
(*     -assert (I_1 : forall (t : tag) (n : nat), lookdown n [] = Some t -> lookup t [] = Some n). *)
(*      { *)
(*        simpl. *)
(*        intros t n H. *)
(*        discriminate. *)
(*      } *)
(*      exact I_1. *)
(*     -assert (I_2 : forall (t : tag) (n : nat), lookdown n (t' :: tl) = Some t -> lookup t (t' :: tl) = Some n). *)
(*      { *)
       




       
(*        intros t0 n. *)
(*        destruct a. *)
(*        -unfold lookdown. *)
(*         destruct (n =? n0). *)
(*         +intro H. *)
(*          inversion H. *)
(*          rewrite <- H1. *)
(*          assert (I_2_1 : forall (t' : tag) (n' : nat) (tl : list (tag * nat)), lookup t' ((t', n') :: tl) = Some n'). *)
(*          { *)
(*            intros t' n' tl. *)
(*            unfold lookup. *)
(*            assert (I_2_1_1 : forall (t'' : tag), tag_beq t'' t'' = true). *)
(*            { *)
(*              destruct t''. *)
(*              -destruct t2. *)
(*               +reflexivity. *)
(*               +reflexivity. *)
(*              -destruct t2. *)
(*               +reflexivity. *)
(*               +reflexivity.                 *)
(*            } *)
(*            rewrite I_2_1_1. *)
(*            reflexivity. *)
(*          } *)
(*          rewrite <- IHt. *)
(*      } *)
        
     
(*   } *)
  
(* Admitted. *)

