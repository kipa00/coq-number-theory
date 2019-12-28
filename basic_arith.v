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