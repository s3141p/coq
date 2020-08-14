From LF Require Export basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity. 
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - destruct m as [| m'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct m as [| m'].
    + simpl. rewrite -> IHn'. reflexivity.
    + simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - destruct m as [| m']. 
    + reflexivity.
    + simpl. 
      rewrite <- plus_n_O.
      reflexivity.
  - destruct m as [| m'].
    + rewrite <- plus_n_O. 
      simpl.
      reflexivity.  
    + simpl. 
      rewrite -> IHn'.
      rewrite -> plus_n_Sm.
      simpl.
      reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n. 
  simpl. 
  reflexivity.
  simpl.
  rewrite -> IHn. 
  reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n.
  - simpl.
    reflexivity.
  - simpl. 
    rewrite -> IHn.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [| n'].  
  - simpl.
    reflexivity.
  - rewrite IHn'. 
    simpl.    
    rewrite -> negb_involutive. 
    reflexivity.
Qed.

Definition manual_grade_for_destruct_induction : option (nat*string) := None.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. 
Qed.

(*
Theorem: true = n =? n for any n. 
Proof: By induction on n. 

* First, suppose n = 0. We must show
  0 =? 0 = true
  This follows directly from the definition of =?.

* Second, suppose n = S n' where
  n' =? n' = true

  We must show
  S n' =? S n' = true
*)

Theorem equal_reflexivity : forall n : nat,
  n =? n = true.
Proof.
  intros.
  induction n.
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> IHn. 
    reflexivity.
Qed.
