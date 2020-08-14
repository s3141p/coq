Set Warnings "-notation-overridden,-parsing".
From LF Require Export tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. 
  injection H as H1.
  apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. 
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n.
  induction n. 
  - split.
    reflexivity.
    destruct m eqn:m'.
    + reflexivity.
    + discriminate.
  - intros. 
    split.
    discriminate.
    discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. 
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. 
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. 
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.  
  apply HP. 
  apply HQ.
  apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn.
    reflexivity.
  - rewrite Hm.
    rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : 
  forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left.
    reflexivity.
  - right. 
    reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
End MyNot.

Theorem ex_falso_quodlibet :
  forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : 
  forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.
  intros P H Q HP.
  destruct H.
  apply HP.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.
  
Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : 
  forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP. 
  destruct HP.
Qed.

Theorem double_neg : 
  forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not. 
  intros G.
  apply G.
  apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. 
  unfold not.
  intros.
  apply H0. 
  apply H.
  apply H1.
Qed.

Theorem not_both_true_and_false : 
  forall P : Prop,
  ~(P /\ ~P).
Proof.
  unfold not.
  intros P contra.
  apply contradiction_implies_anything with(P:=P).
  apply contra.
Qed.

Theorem not_true_is_false : 
  forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. 
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso. 
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB. 
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H.
    rewrite H.
    intros H'.
    discriminate H'.
Qed.

Theorem or_distributes_over_and : 
  forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split. 
  - intros.
    destruct H.
    + split.
      left. apply H.
      left. apply H.
    + split.
      destruct H.
      right. apply H.
      destruct H.
      right. apply H0.
  - intros.
    destruct H as [HL HR].
    destruct HL.
    destruct HR.
    left. 
    apply H.
    left.
    apply H.
    destruct HR.
    left.
    apply H0.
    right.
    split.
    apply H.
    apply H0.
Qed. 

From Coq Require Import Setoids.Setoid.

Lemma or_assoc :
  forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros.
    destruct H as [H | [H | H]]. 
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. 
  destruct n.
  - left.
    reflexivity. 
  - destruct m. 
    + right. 
      reflexivity.
    + discriminate.
Qed. 

Lemma mult_0 :
  forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma mult_0_3 :
  forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. 
  rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. 
  apply mult_0. 
  apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl.
    intros [].
  - simpl.
    intros [H | H].
    + rewrite H.
      left.
      reflexivity.
    + right.
      apply IHl'.
      apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros.
  split.
  induction l.
  - simpl. 
    intros [].
  - simpl.
    intros [H | H].
    + exists x. 
      split. 
      apply H. 
      left.
      reflexivity.
    + apply IHl in H. 
      destruct H as [w [F I]].
      exists w. 
      split. 
      apply F.
      right.
      apply I.
  - intros [w [F I]].
    rewrite <- F.
    apply In_map.
    apply I.
Qed.

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
    | [] => True
    | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <->
  All P l.
Proof.
  intros.
  split.
  - induction l.
    + intros.
      simpl.
      reflexivity.
    + intros.
      simpl.
      split.
      apply H.
      * simpl.
        left.
        reflexivity.
      * apply IHl.
        intros.
        apply H.
        simpl.
        right.
        apply H0.
  - induction l. 
    + simpl.
      intros.
      exfalso.
      apply H0.
    + simpl.
      intros [H H0] x' [H1 | H1].
      * rewrite <- H1. 
        apply H.
      * apply IHl.
        apply H0.
        apply H1.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (fun x => if oddb x then Podd x else Peven x).

Theorem combine_odd_even_intro :
  forall(Podd Peven : nat -> Prop) (n : nat),
  (oddb n = true -> Podd n) ->
  (oddb n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros.
  destruct (oddb n) eqn:H1.
  - unfold combine_odd_even.
    rewrite H1.
    apply H.
    reflexivity.
  - unfold combine_odd_even.
    rewrite H1.
    apply H0.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall(Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = true ->
  Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall(Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = false ->
  Peven n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Check plus_comm.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A),
  In x l -> l <> [].
Proof.
  intros A x l H. 
  unfold not.
  intro Hl.
  destruct l.
  - simpl in H.
    destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat,
  In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat,
  In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, 
  In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat,
  In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat,
  In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
  In n (map (fun m => m * 0) ns) ->
  n = 0.
Proof.
  intros n ns H.
  destruct 
  (proj1 _ _ (In_map_iff _ _ _ _ _) H) as
  [m [Hm _]].
  rewrite mult_0_r in Hm.
  rewrite <- Hm.
  reflexivity.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Axiom functional_extensionality : 
  forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_order :
  forall X (l1 l2 l3: list X),
  rev_append l1 l2 ++ l3 = rev_append l1 (l2 ++ l3). 
Proof.
  induction l1.
  - reflexivity.
  - intros.
    destruct l2.
    + apply IHl1.  
    + apply IHl1. 
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  induction x.
  - unfold tr_rev.
    reflexivity.
  - simpl.  
    rewrite <- IHx.
    unfold tr_rev.
    simpl.
    rewrite rev_append_order.
    simpl.
    reflexivity.
Qed.

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. 
  induction k as [|k' IHk'].
  - reflexivity.
  - simpl.
    apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, 
  n = if evenb n then double k
                else S (double k).
Proof.
  induction n.
  - exists 0.
    reflexivity.
  - rewrite evenb_S.     
    destruct IHn as [k' H].
    destruct (evenb n).
    + simpl.
      rewrite H.
      exists k'.
      reflexivity.
    + simpl.
      exists (S k').
      rewrite H.
      reflexivity.
Qed.
       
Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n.
  split.
  - intros H.
    destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk.
    rewrite H.
    exists k. 
    reflexivity.
  - intros [k Hk].
    rewrite Hk.
    apply evenb_double.
Qed.

Lemma eqb_refl: 
  forall x: nat,
  (x =? x) = true.
Proof.
  intros.
  induction x.
  reflexivity.
  simpl.
  apply IHx.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. 
    rewrite H.
    rewrite <- eqb_refl with(x:=n2).
    reflexivity.
Qed.

Example not_even_1001 : evenb 1001 = false.
Proof.
  reflexivity.
Qed.

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split. 
  - intros. 
    split.
    + destruct b1.
      * reflexivity.
      * discriminate.
    + destruct b2.
      * reflexivity.
      * destruct b1.
        discriminate.
        discriminate.
  - intros.
    destruct  H. 
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  split. 
  - intros. 
    destruct H.
    destruct b1.
    + left. 
      reflexivity.
    + right.
      reflexivity.
  - intros [H1 | H2].
    + rewrite H1.
      reflexivity.
    + rewrite H2.
      destruct b1.
      reflexivity.
      reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- not_true_iff_false.
  rewrite -> eqb_eq.
  reflexivity.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, h' :: t' => false
  | h :: t, nil => false
  | h :: t, h' :: t' => eqb h h' && eqb_list eqb t t'
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1.
  - destruct l2.
    * simpl.
      split.
      + intros.
        reflexivity.
      + intros.
        reflexivity.
    * simpl.  
      split.
      + intros.
        discriminate.
      + intros.
        discriminate.
  - destruct l2.
    * simpl. 
      split.
      + intros.
        discriminate.
      + intros.
        discriminate.
    * simpl.
      split.
      + intros. 
        apply andb_true_iff in H0.
        destruct H0 as [H1 H2].
        apply H in H1.
        apply IHl1 in H2.
        rewrite H1, H2.
        reflexivity.
      + intros.
        injection H0 as H1 H2.
        apply H in H1.
        rewrite H1.
        apply IHl1.
        apply H2.
Qed.

Theorem forallb_true_iff : 
  forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  induction l.
  - split.
    + simpl.
      reflexivity.
    + simpl. 
      reflexivity.
  - split.
    + intros.
      simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      rewrite IHl in H2.
      simpl.
      split.
      * apply H1.
      * apply H2.
    + intros. 
      simpl in H.
      destruct H as [H1 H2].
      simpl.
      rewrite H1.
      apply IHl.
      apply H2.
Qed.
