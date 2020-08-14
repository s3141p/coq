Set Warnings "-notation-overridden,-parsing".
From LF Require Export poly.

Theorem silly1 : forall(n m o p : nat),
  n = m ->
  [n;o] = [n;p] -> 
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall(n m o p : nat),
  n = m-> 
  (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall(n m : nat),
  (n,n) = (m,m) -> 
  (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) -> 
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Lemma modus_ponens:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H.
  assumption.
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  oddb 3 = true ->
  evenb 4 = true.
Proof.
  intros. 
  apply H0. 
Qed.

Theorem silly3_firsttry : forall(n : nat),
  true = (n =? 5) -> 
  (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H.
Qed.

Theorem rev_exercise1 : forall(l l' : list nat),
  l = rev l' -> 
  l' = rev l.
Proof.
  intros .
  rewrite -> H. 
  symmetry.
  apply rev_involutive. 
Qed.

Example trans_eq_example : forall(a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] -> 
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall(X:Type) (n m o : X),
  n = m ->
  m = o ->
  n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall(a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c;d].
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall(n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m.
  apply H0.
  apply H.
Qed.

Theorem S_injective : forall(n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. 
  rewrite H1.
  reflexivity.
Qed.

Theorem S_injective' : forall(n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H.
  intros Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall(n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. 
  intros H1 H2.
  rewrite H1. 
  rewrite H2. 
  reflexivity.
Qed.

Theorem injection_ex2 : forall(n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  rewrite Hnm.
  reflexivity. 
Qed.

Example injection_ex3 : forall
  (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros .
  injection H0.
  intros.
  symmetry.
  apply H2.
Qed.

Theorem eqb_0_l : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - simpl.
    intros H.
    discriminate H.  
Qed.

Theorem discriminate_ex1 : forall(n : nat),
  S n = O -> 
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : forall(n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Example discriminate_ex3 :
  forall(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem f_equal : forall(A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. 
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem S_inj : forall(n m : nat) (b : bool),
  (S n) =? (S m) = b ->
  n =? m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall(n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n'].
  - simpl.
    intros. 
    destruct m.
    + reflexivity.
    + discriminate.
  - intros. 
    destruct m.
    + discriminate.
    + inversion H. 
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn' in H2.
      rewrite -> H2.
      reflexivity.
Qed.

Theorem double_injective: forall n m,
  double n = double m -> n = m. 
Proof.
  intros n. 
  induction n as [| n'].
  - simpl.
    intros m eq. 
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + simpl.
      discriminate eq.
    + apply f_equal.
      apply IHn'.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - destruct m. 
    + simpl.
      reflexivity.
    + simpl.
      discriminate.
  - intros m.  
    destruct m.
    + simpl. 
      discriminate.
    + simpl.
      intros H.
      apply f_equal.
      apply IHn'.
      apply H.
Qed.

Definition manual_grade_for_informal_proof : option (nat*string) := None.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl.
    intros n eq.
    destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros n eq.
    destruct n as [| n'] eqn:E.
    + discriminate eq.
    + apply f_equal.
      apply IHm'.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n].
  simpl.
  intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'.
  reflexivity.
Qed.

Theorem nth_error_after_last: 
  forall(n : nat) (X : Type) (l : list X),
  length l = n -> 
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h l' IHl'].
  - simpl.
    reflexivity.
  - destruct n as [| n']. 
    + simpl.     
      discriminate.
    + simpl.
      intros H.
      apply IHl'.
      injection H.
      intros H1.
      apply H1.
Qed.

Definition square n := n * n.
Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m,
  foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  reflexivity.
  reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : 
  forall(n : nat),
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - reflexivity.
    - destruct (n =? 5) eqn:E2.
      + reflexivity.
      + reflexivity. 
Qed.

Theorem combine_split : 
  forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> 
  combine l1 l2 = l.
Proof.
  intros X Y.
  induction l as [| [x y] l'].
  + simpl. 
    intros l1 l2 H.
    injection H.
    intros H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    reflexivity.
  + intros l1 l2.
    simpl.
    intros H.
    inversion H.
    simpl.
    rewrite IHl'.
    reflexivity.
    destruct (split l').
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall(n : nat),
  sillyfun1 n = true -> 
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
   - apply eqb_true in Heqe3.
     rewrite -> Heqe3. 
     reflexivity.
  - destruct (n =? 5) eqn:Heqe5.
      + apply eqb_true in Heqe5.
        rewrite -> Heqe5. reflexivity.
      + discriminate eq.
Qed.


Theorem bool_fn_applied_thrice :
  forall(f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct b.
  - destruct (f true) eqn: HFT. 
    + rewrite HFT.
      rewrite HFT.
      reflexivity.
    + destruct (f false) eqn: HFF.
      * rewrite HFT.
        reflexivity.
      * rewrite HFF.
        reflexivity.
  - destruct (f false) eqn: HFF.
    + destruct (f true) eqn: HFT.
      * rewrite HFT.
        reflexivity.
      * rewrite HFF.
        reflexivity.
    + rewrite HFF.
      rewrite HFF.
      reflexivity.
Qed.


Theorem eqb_sym : forall(n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n.
  - destruct m.
    + reflexivity.
    + reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. 
      apply IHn.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p.
  intros H H1.
  apply eqb_true in H.
  apply eqb_true in H1.
  rewrite H.  
  rewrite H1.
  rewrite equal_reflexivity.
  reflexivity.
Qed.

Definition split_combine_statement : Prop :=
  forall (X Y: Type) (l1: list X) (l2: list Y), 
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1.
  - simpl.
    destruct l2.
    + simpl.
      reflexivity.
    + discriminate.
  - intros l2 H. 
    destruct l2.
    + discriminate H.
    + injection H.  
      intros H1.
      apply IHl1 in H1.
      simpl.
      rewrite H1.
      simpl.
      reflexivity.
Qed.

Definition manual_grade_for_split_combine : option (nat*string) := None.

Theorem filter_exercise : 
  forall(X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X fb x l.
  generalize dependent fb.
  generalize dependent x.
  induction l.
  - destruct lf.
    + discriminate. 
    + discriminate. 
  - simpl.
    intros.
    destruct (fb x) eqn:Fun.
    + inversion H. 
      rewrite <- H1.
      apply Fun.
    + simpl. 
      apply IHl in H. 
      rewrite H.
      reflexivity.
Qed.

Fixpoint forallb 
  {X: Type} (test: X -> bool) (l: list X): bool :=  
  match l with 
  | nil => true
  | h :: t => if test h 
      then forallb test t
      else false
  end.

Fixpoint existsb 
  {X: Type} (test: X -> bool) (l: list X): bool :=  
  match l with 
  | nil => false
  | h :: t => if test h 
      then true
      else existsb test t
  end.

Definition existsb' 
  {X : Type} (test : X -> bool) (l : list X) : bool :=
  leb 1 (length (filter test l)).

Example forall1: forallb oddb [1;3;5;7;9] = true.
Proof. simpl. reflexivity. Qed.

Example forall2: forallb negb [false;false] = true.
Proof. simpl. reflexivity. Qed.
       
Example forall3: forallb evenb [0;2;4;5] = false.
Proof. simpl. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. simpl. reflexivity. Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. simpl. reflexivity. Qed.

Theorem existsb_existsb' : 
  forall(X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  generalize dependent test.
  induction l.
  - intros.
    unfold existsb'.
    simpl.
    reflexivity.
  - intros.
    destruct (test x) eqn:t.
    + unfold existsb'. 
      simpl.
      rewrite t.
      simpl.
      reflexivity.
    + simpl.
      rewrite t.
      rewrite IHl.
      unfold existsb'.
      simpl.
      rewrite t.
      reflexivity.
Qed.
