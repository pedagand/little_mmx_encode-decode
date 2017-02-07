Require Import Arith List Recdef.

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

