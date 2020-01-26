Require Export basic_arith.

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

Lemma le_plus_trivial : forall n m, n <= n + m.
Proof.
  intros; rewrite (plus_comm n m). induction m; simpl; eauto.
Qed.

Lemma le_trans : forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  intros x y; revert x. induction y; intros.
  + destruct x; try inversion H; assumption.
  + destruct x; destruct z;
    repeat match goal with
    | H : S _ <= 0 |- _ => inversion H
    | H : S _ <= S _ |- _ => apply le_rev in H
    | |- 0 <= S ?z => clear; induction z; eauto
    | |- S _ <= S _ => apply le_prog
    end. apply IHy; assumption.
Qed.

Lemma le_contra : forall n m, S m + n <= n -> False.
Proof.
  intros n m; revert n. induction m; induction n; intros.
  + inversion H.
  + apply le_rev in H. destruct (IHn H).
  + replace (S (S m) + 0) with (S (S m)) in H
    by (clear; induction m; eauto). inversion H.
  + rewrite <- plus_n_Sm in H; apply le_rev in H. destruct (IHn H).
Qed.

Lemma minus_plus_cancel: forall n m, n >= m -> n - m + m = n.
Proof.
  intro n. induction n; intros; destruct m; eauto.
  + inversion H.
  + apply le_rev in H. simpl. rewrite plus_comm. simpl. rewrite plus_comm.
    rewrite IHn; try reflexivity; assumption.
Qed.

Lemma le_zero_refl : forall n m, n >= m <-> m - n = 0.
Proof.
  intro n; induction n; intros; split; intros; destruct m; eauto.
  + inversion H.
  + simpl in *. inversion H.
  + simpl. apply le_rev in H. apply IHn; assumption.
  + clear; induction n; eauto.
  + apply le_prog; apply IHn; apply H.
Qed.