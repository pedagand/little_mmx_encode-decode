Require Import Arith List Recdef.

Lemma ex1 : forall x : nat, forall A B : Prop,
   A /\ B -> A \/ 3 * x = x + x + x.
Proof.
intros x a b ab.
destruct ab as [h1 h2].
left.
exact h1.
Qed.

Lemma ex2 : forall A B : Prop, A \/ B -> B \/ A.
Proof.
intros a b ab; destruct ab as [ha | hb].
  right; assumption.
left; assumption.
Qed.

Lemma ex3 : forall A B : Prop, A -> (A -> B) -> A /\ B.
Proof.
intros A B.
intros ha h_a_implies_b.
split.
  exact ha.
apply h_a_implies_b.
exact ha.
Qed.

Lemma ex4 : exists x: nat, (True /\ 2 * x + 2 = 10).
Proof.
exists 4.
split.
  trivial.
  reflexivity.
Qed.

Fixpoint ltn (l : list bool) : nat :=
  match l with 
    nil => 0 
  | a::tl => (if a then 1 else 0) + 2 * ltn tl
  end.

Function ntl (n : nat) {wf lt} :=
  match n with
    0 => nil
  | S p =>  negb (Nat.even n) :: ntl (Nat.div2 n)
  end.
intros n p nsp; apply Nat.lt_div2.
auto with arith.
exact lt_wf.
Qed.

Lemma toto : ntl 32 = false::false::false::false::false::true::nil.
rewrite 7!ntl_equation; simpl; reflexivity.
Qed.

Lemma titi n : ltn (ntl n) = n.
Proof.
induction n using (well_founded_ind lt_wf).
rewrite ntl_equation.
case_eq n.
  trivial.
intros p n_is_Sp.
change ((if negb (Nat.even (S p)) then 1 else 0) +
        2 * ltn (ntl (Nat.div2 (S p))) = S p).
rewrite H; cycle 1.
  rewrite n_is_Sp; apply Nat.lt_div2; auto with arith.

Lemma toto : ntl 4 = true::false::false::nil.
rewrite 4!ntl_equation; simpl.
Check ntl_terminate.
Search Nat.div2.
Search (list bool).
Check Nat.bitwise.


Definition ntl (n : nat) :=
  Fix lt_wf (fun _ => list bool)
  (fun x ntl =>
     match zerop x with
       left _ => nil
     | right h => negb(Nat.even x) :: 
                  ntl (Nat.div2 x) (Nat.lt_div2 _ h)
end).

Check Fix.

