Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  intros n. induction n; intros; eauto.
  induction m; eauto. simpl.
  rewrite (IHn (S m)). rewrite <- IHm. simpl.
  replace (m + n) with (n + m) by apply IHn; eauto.
Qed.

Lemma plus_assoc : forall n m k, n + (m + k) = n + m + k.
Proof.
  intros; induction n; simpl; eauto.
Qed.

Lemma mul_comm : forall n m, n * m = m * n.
Proof.
  intros n. induction n; eauto. induction m; eauto.
  simpl. rewrite (IHn (S m)); rewrite <- IHm. simpl.
  rewrite (IHn m). repeat rewrite plus_assoc. rewrite (plus_comm m n); eauto.
Qed.

Lemma plus_mul_dist : forall n m k, n * (m + k) = n * m + n * k.
Proof.
  intros; induction k.
  + rewrite plus_comm. rewrite (mul_comm _ 0). simpl.
    rewrite plus_comm. eauto.
  + rewrite plus_comm. rewrite (mul_comm n (_ + _)).
    rewrite (mul_comm _ (S _)). simpl.
    rewrite mul_comm. rewrite (plus_comm k m). rewrite IHk.
    rewrite (plus_assoc (n * m) _). rewrite (plus_comm _ n).
    rewrite plus_assoc. rewrite (mul_comm n k). eauto.
Qed.

Lemma mul_assoc : forall n m k, n * (m * k) = n * m * k.
Proof.
  intros; induction n; simpl; eauto.
  rewrite (mul_comm (_ + _) k); rewrite plus_mul_dist; rewrite (mul_comm k _).
  rewrite (mul_comm k _). rewrite IHn; eauto.
Qed.

Lemma le_prog : forall n m, n <= m -> S n <= S m.
Proof.
  intros n. induction n; intros.
  + clear H. induction m; eauto.
  + induction m; inversion H; eauto.
Qed.

Lemma le_rev : forall n m, S n <= S m -> n <= m.
Proof.
  intros n. induction n; intros.
  + clear H. induction m; eauto.
  + induction m; inversion H; eauto. inversion H1.
Qed.

Lemma strong_natind_lim : forall (P : nat -> Prop) (lim : nat),
  (forall n, (forall k, k < n -> P k) -> P n)
  -> (forall n, n < lim -> P n).
Proof.
  intros P lim; revert P. induction lim.
  + intros. destruct n; inversion H0.
  + intros. inversion H0; subst; clear H0.
    - specialize (IHlim P H). exact (H lim IHlim).
    - assert (n < lim). { assumption. } clear H2.
      exact (IHlim P H n H0).
Qed.

Lemma strong_natind : forall (P : nat -> Prop),
  (forall n, (forall k, k < n -> P k) -> P n) -> forall n, P n.
Proof.
  intros. assert (n < S n). { eauto. }
  exact (strong_natind_lim P (S n) H n H0).
Qed.

Lemma plus_le : forall n m, n <= n + m.
Proof.
  intro n. induction n.
  + intros. induction m; simpl in *; eauto.
  + intros. specialize (IHn m). simpl. apply le_prog. assumption.
Qed.

Lemma minus_plus_cancel: forall n m, n >= m -> n - m + m = n.
Proof.
  intro n. induction n; intros; destruct m; eauto.
  + inversion H.
  + apply le_rev in H. simpl. rewrite plus_comm. simpl. rewrite plus_comm.
    rewrite IHn; try reflexivity; assumption.
Qed.

Lemma plus_minus_cancel: forall n m, m + n - m = n.
Proof.
  intro n. induction n; intros; induction m; eauto.
Qed.