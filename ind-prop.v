Set Warnings "-notation-overridden,-parsing".
From LF Require Export logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS (n : nat) (H : even n) : even (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).

Inductive even' : nat -> Prop :=
  | ev_0' : even' 0
  | ev_SS' : forall n, even' n -> even' (S (S n)). 

Theorem ev_4 : even 4.
Proof. 
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4' : even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 :
  forall n, even n -> even (4 + n).
Proof.
  intros n. 
  simpl.
  intros Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.

Theorem ev_double :
  forall n,
  even (double n).
Proof.
  induction n.
  - simpl.
    apply  ev_0.
  - simpl.
    apply ev_SS.
    apply IHn.
Qed.

Theorem ev_inversion :
  forall(n : nat), even n ->
  (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - left.
    reflexivity.
  - right.
    exists n'.
    split.
    reflexivity.
    apply E'.
Qed.

Theorem ev_minus2 : 
  forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - simpl.
    apply ev_0.
  - simpl.
    apply E'.
Qed.

Theorem evSS_ev : 
  forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  destruct E as [| n' E'].
Abort.

Theorem evSS_ev : 
  forall n, 
  even (S (S n)) -> even n.
Proof. 
  intros n H.
  apply ev_inversion in H. 
  destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]].
   injection Hnm.
   intro Heq.
   rewrite Heq.
   apply Hev.
Qed.

Theorem evSS_ev' : 
  forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ even 1.
Proof.
  intros H. 
  apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem SSSSev__even : 
  forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem SSSSev__even' : 
  forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H.
  + discriminate.
  + destruct H. 
    destruct H.
    injection H.
    intros.
    apply ev_inversion in H0.
    destruct H0.
    - rewrite H0 in H1.
      discriminate.
    - destruct H0.
      destruct H0.
      rewrite H0 in H1.
      injection H1.
      intros. 
      rewrite <- H3 in H2.
      apply H2.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1 :
  forall(n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. 
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 :
  forall(n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Lemma ev_even_firsttry :
  forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  inversion E as [| n' E'].
  - exists 0.
    reflexivity.
  - simpl.
    assert (I : (exists k', n' = double k') ->
           (exists k, S (S n') = double k)).
   { intros [k' Hk']. 
     rewrite Hk'. exists(S k').
     reflexivity. }
   apply I.
Abort.

Lemma ev_even : 
  forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0.
    reflexivity.
  - destruct IH as [k' Hk'].
    rewrite Hk'.
    exists(S k').
    reflexivity.
Qed.

Theorem ev_even_iff : 
  forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. 
  split.
  - apply ev_even.
  - intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.

Theorem ev_sum : 
  forall n m,
  even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn.
  - simpl.
    apply Hm.
  - inversion Hm. 
    + simpl.
      rewrite <- plus_n_O.
      apply ev_SS.
      apply Hn.
    + simpl.
      apply ev_SS.
      rewrite H0.
      apply IHHn.
Qed.

Inductive even'' : nat -> Prop :=
  | even'_0 : even'' 0
  | even'_2 : even'' 2
  | even'_sum n m (Hn : even'' n) (Hm : even'' m) : even'' (n + m).

Theorem even'_ev :
  forall n, 
  even'' n <-> even n.
Proof.
  intros n.
  split.
  + intros.
    induction H.
    - apply ev_0.
    - apply ev_SS.
      apply ev_0.
    - apply ev_sum.
      apply IHeven''1.
      apply IHeven''2.
  + intros.
    induction H.
    - apply even'_0.
    - assert (H1: (S (S n)) = 2 + n). 
      * reflexivity.
      * rewrite H1.
        apply (even'_sum 2 n).
        apply even'_2.
        apply IHeven.
Qed.

Theorem ev_ev__ev : 
  forall n m,
  even (n + m) -> even n -> even m.
Proof.
  intros.
  induction H0. 
  - apply H.
  - inversion H. 
    apply IHeven.
    apply H2.
Qed.

Theorem ev_plus_plus : 
  forall n m p,
  even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros n m p H.
  apply ev_ev__ev. 
  rewrite plus_comm.
  Search plus.
  rewrite PeanoNat.Nat.add_shuffle3.
  rewrite <- plus_assoc.
  rewrite plus_assoc.
  apply ev_sum.
  apply H.
  rewrite <- double_plus.
  apply ev_double.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m ≤ n" := (le m n)
(at level 50).

Theorem test_le1 :
  3 ≤ 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 ≤ 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le3 :
  (2 ≤ 1) -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=.

Lemma le_trans : 
  forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros.
  rewrite H.
  apply H0.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - reflexivity.
  - apply le_S.
    apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - rewrite <- H1.
    apply le_S.
    reflexivity.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction a.
  - apply O_le_n.
  - intros b.
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHa.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros.
  split.
  - rewrite <- H.
    apply le_plus_l.
  - rewrite <- H.
    rewrite plus_comm.
    apply le_plus_l.
Qed.

Theorem lt_succ_r p q : p < S q <-> p <= q.
Proof.
  split.
  - induction p. 
    + intros.
      apply O_le_n.
    + intros.
      apply Sn_le_Sm__n_le_m in H.
      apply H.
  - induction p. 
    + intros.
      unfold lt.
      apply n_le_m__Sn_le_Sm.
      apply H.
    + intros.
      unfold lt.
      apply n_le_m__Sn_le_Sm.
      apply H.
Qed.

 Theorem lt_S : 
   forall n m,
   n < m ->
   n < S m.
Proof.
  intros.
  unfold lt in H.
  unfold lt.
  apply le_S in H.
  apply H.
Qed.

Theorem plus_lt :
  forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros.
  unfold "<" in H.
  unfold "<".
  induction H.
  - split. 
    * apply n_le_m__Sn_le_Sm. 
      apply le_plus_l.
    * apply n_le_m__Sn_le_Sm.
      rewrite plus_comm.
      apply le_plus_l.
  - split.
    * apply le_S.
      apply IHle.
    * apply le_S.
      apply IHle.
Qed.

Theorem leb_complete : 
  forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n.
  - induction m.
    + simpl.
      intros.
      reflexivity.
    + intros.
      apply le_S.
      apply IHm.
      unfold "<=?".
      reflexivity.
  - induction m.
    + unfold "<=?".
      intros.
      inversion H.
    + intros.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      inversion H.
      reflexivity.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m.
  generalize n as n'.
  induction m. 
  - intros. 
    destruct n'.
    + reflexivity.
    + inversion H. 
  - intros.
    induction n'.
    + reflexivity.
    + apply Sn_le_Sm__n_le_m in H.
      apply IHm in H.
      apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_correct. 
  apply leb_complete in H.
  apply leb_complete in H0.
  rewrite H.
  apply H0.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros.
  split.
  - intros.
    apply leb_complete.
    apply H.
  - intros.
    apply leb_correct.
    apply H.
Qed.

Module R.
  
