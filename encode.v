Require Import Bool List Arith Nat.
Require Import ast_instructions.
Require Import binary.
Import ListNotations.

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
Definition encdec : tag_opcode_assoc := [(tag_n(ADD),1);(tag_n(AND),2);(tag_i(ADD_I),3);(tag_i(AND_I),4)].

Theorem lookup_encdec : forall (t : tag), exists n,
                          lookup t encdec = Some n.
Proof.
  destruct t.
  -destruct t.
   +simpl. exists 1. reflexivity.
   +simpl. exists 2. reflexivity.
  -destruct t.
   +simpl. exists 3. reflexivity.
   +simpl. exists 4. reflexivity.
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

(* if i wan't it's very easy to proof with forall t exists n but this theorem is better and actually it's true *)
Theorem look_down_up_encdec : forall (n : nat) (t : tag),
                                lookdown n encdec = Some t -> lookup t encdec = Some n.
Proof.
  assert (I : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n).
  {
    intros n t.
    destruct (lookdown n encdec).
    {destruct t0.
     -destruct t0.
      +intros H.
       simpl in H.
       inversion H.
       
    } 
  }






    
