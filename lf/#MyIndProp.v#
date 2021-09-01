Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.

Inductive ev: nat -> Prop :=
  | ev_0: ev 0
  | ev_SS (n: nat)(H: ev n) : ev (S (S n)).

Theorem ev_double : forall n,
  ev (double n).
Proof.
  induction n as [| n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

Theorem ev_inversion: forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split.
    + reflexivity.
    + apply E'.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - simpl. apply E.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - Abort.

Theorem evSS_ev_remember: forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  remember (S (S n)) as k eqn:Hk.
  destruct E as [ | n' E'] eqn:EE.
  - discriminate Hk.
  - injection Hk as H. rewrite <- H. apply E'.
Qed.

Theorem evSS_ev: forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  apply ev_inversion in E as H.
  destruct H as [ H | H ].
  - discriminate H.
  - destruct H as [n' [H1 H2]]. injection H1 as H1.
     rewrite H1. apply H2.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [ | n' E' Heq].
  apply E'.
Qed.

Theorem one_not_even: ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [H | [n' [H1 H2]]].
  - discriminate H.
  - injection H1 as H1. discriminate H1.
Qed.

Theorem one_not_even': ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even: forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  remember (S (S (S (S n)))) as k eqn:Hk.
  destruct E.
  - discriminate Hk.
  - injection Hk as Hk. rewrite Hk in E. 
     apply evSS_ev in E. apply E.
Qed.

Theorem ev5_nonsense:
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  apply SSSSev__even in E.
  inversion E.
Qed.

Theorem inversion_ex_1: forall (n m o: nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex_2: forall (n: nat),
  S n = 0 -> 2 + 2 = 5.
Proof. intros n H. inversion H. Qed.

Lemma ev_Even_firsttry: forall n,
  ev n -> even n.
Proof.
  unfold even.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - exists 0. simpl. reflexivity.
  - assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    {
      intros [k' EQ'']. exists (S k'). simpl. rewrite <- EQ''. reflexivity.
    }
    apply H.
    generalize dependent E'.
Abort.

Lemma ev_even: forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [ | n' E' IHE'].
  - unfold even. exists 0. simpl. reflexivity.
  - unfold even in IHE'. destruct IHE' as [k Hk]. 
     rewrite Hk. unfold even. exists (S k).
     simpl. reflexivity.
Qed.

Theorem ev_Even_iff: forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  - apply ev_even.
  - intros H. unfold even in H. destruct H as [k Hk].
     rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum: forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m E.
  induction E as [| n' E' IHE'].
  - simpl. intros H. apply H.
  - simpl. intros H. apply ev_SS. 
     apply IHE' in H. apply H.
Qed.

Inductive ev': nat -> Prop :=
  | ev'_0: ev' 0
  | ev'_2: ev' 2
  | ev'_sum n m (Hn: ev' n) (Hm: ev' m): ev' (n + m).

Lemma SS_plus_2: forall n,
  S (S n) = 2 + n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem ev'_ev: forall n,
  ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros E. induction E as [| | n' m' E' IHE1'].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHE1'.
      * apply IHE1.
  - intros E. induction E as [ | n' E' IHE'].
    + apply ev'_0.
    + rewrite SS_plus_2. apply ev'_sum.
      * apply ev'_2.
      * apply IHE'.
Qed.

Theorem sum_ev: forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E1 E2.
  generalize dependent E1.
  induction E2 as [ | n' E' IHE'].
  - simpl. intros H. apply H.
  - simpl. intros H. apply IHE'. apply evSS_ev.
    apply H.
Qed.

Lemma l1: forall n m p,
  (n + m) + (n + p) = (n + n) + (m + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  assert (H: (n + m + n) = (n + n + m)).
  - rewrite plus_comm. rewrite plus_assoc. reflexivity.
  - rewrite H. rewrite <- plus_assoc. reflexivity.
Qed.

Theorem ev_plus_plus: forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p.
  intros E1 E2.
  assert (H1: ev ((n + m) + (n + p))).
  {
    apply ev_sum.
    - apply E1.
    - apply E2.
  }
  rewrite l1 in H1.
  apply (sum_ev (n + n) (m + p)) in H1.
  + apply H1.
  + rewrite <- double_plus. apply ev_double.
Qed.

Print le.

Lemma le_trans: forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros H1 H2.
  induction H2 as [| n' E IHE'].
  - apply H1.
  - apply le_S. apply IHE'.
Qed.

Theorem O_le_n: forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m E.
  induction E.
  - apply le_n.
  - apply le_S. apply IHE.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m E.
  inversion E.
  - apply le_n.
  - apply (le_trans n (S n)).
    + apply le_S. apply le_n.
    + apply H0.
Qed.

Theorem lt_ge_cases :forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  unfold lt.
  unfold ge.
  induction m.
  - right. apply O_le_n.
  - induction n.
    + destruct IHm as [IHm | IHm].
      * left. apply le_S. apply IHm.
      * inversion IHm.
        -- left. apply le_n.
    + Abort.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction a.
  intros.
  - simpl. apply O_le_n.
  - intros b. simpl. apply n_le_m__Sn_le_Sm.
     apply IHa.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  intros.
  split.
  - apply (le_trans n1 (n1 + n2)).
    + apply le_plus_l.
    + apply H.
  - apply (le_trans n2 (n1 + n2)).
    + rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem Sn_le_m__n_le_m: forall n m,
  S n <= m -> n <= m.
Proof.
  intros n m E.
  induction E.
  - apply le_S. apply le_n.
  - inversion E.
    + apply le_S. apply le_S. apply le_n.
    + apply le_S. apply le_S.
      apply (le_trans n (S n)).
      * apply le_S. apply le_n.
      * apply H.
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n.
  - intros. left. apply O_le_n.
  - intros. destruct p.
    + simpl in H. right. apply Sn_le_m__n_le_m in H.
      apply plus_le in H. destruct H as [_ H]. apply H.
    + simpl in H. apply Sn_le_Sm__n_le_m in H.
      apply IHn in H. destruct H as [H | H].
      * left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply H.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m -> p + n <= p + m.
Proof.
  intros n m p E.
  induction E.
  - apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IHE.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  intros n m p.
  rewrite (plus_comm n p).
  rewrite (plus_comm m p).
  apply plus_le_compat_l.
Qed.

Theorem le_plus_trans: forall n m p,
  n <= m -> n <= m + p.
Proof.
  intros n m p E.
  induction E.
  - apply le_plus_l.
  - simpl. apply le_S. apply IHE.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m -> n <= m.
Proof.
  unfold lt.
  apply Sn_le_m__n_le_m.
Qed.

Theorem plus_lt: forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m.
  intros H.
  split.
  - replace (S (n1 + n2)) with ( (S n1) + n2) in H.
    + apply plus_le in H. destruct H as [H _]. apply H.
    + simpl. reflexivity.
  - replace (S (n1 + n2)) with ( (S n2) + n1) in H.
    + apply plus_le in H. destruct H as [H _]. apply H.
    + simpl. f_equal. apply plus_comm.
Qed.

Theorem leb_complete: forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m.
  - induction n.
    + intros. apply le_n.
    + intros. inversion H.
  - intros n H. induction n.
    + apply O_le_n.
    + simpl in H. apply IHm in H. apply n_le_m__Sn_le_Sm.
      apply H.
Qed.

Theorem n_leb_m__n_leb_Sm: forall n m,
  n <=? m = true -> n <=? S m = true.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. destruct m.
    + discriminate H.
    + simpl in H. apply IHn in H. simpl. apply H.
Qed.


Theorem leb_correct: forall n m,
  n <= m -> n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros n H. simpl. inversion H.
    + simpl. reflexivity.
  - intros n H. simpl. inversion H.
    + simpl. rewrite <- leb_refl. reflexivity.
    + apply IHm in H1. apply n_leb_m__n_leb_Sm.
      apply H1.
Qed.

Theorem leb_true_trans: forall n m o,
  n <=? m = true -> m <=? o = true ->
    n <=? o = true.
Proof.
  intros n m o.
  intros H1 H2.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_correct.
  apply (le_trans n m o).
  - apply H1.
  - apply H2.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o
.

Example R_can_prove: R 1 1 2.
  Proof. apply c2. apply c5. apply c2. apply c1. Qed.

Example R_proof_2: R 2 2 6.
  Proof. apply c2. apply  c2. apply c5. apply c2. Abort.

Definition fR: nat -> nat -> nat
  := fun x y => x + y.

Theorem R_equiv_fR: forall m n o,
  R m n o <-> fR m n = o.
Proof.
  unfold fR.
  intros m n o.
  split.
  (* -> *)
  - intros H.
    induction H.
    + simpl. reflexivity.
    + simpl. rewrite IHR. reflexivity.
    + simpl. rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR.
      inversion IHR. reflexivity.
    + rewrite plus_comm. apply IHR.
  - generalize dependent o. generalize dependent n.
    induction m.
    + simpl. induction n.
      * intros. rewrite <- H. apply c1.
      * intros o. destruct o. 
        -- intros. rewrite H. apply c1.
        -- intros. apply c3. inversion H. apply IHn in H1 as H2. rewrite H1 in H2. apply H2.
    + intros. simpl in H. rewrite <- H. apply c2. apply IHm. reflexivity.
Qed.
























