Require Export basic_arith.
Require Export inequality.

Ltac refl := try reflexivity.
Ltac tinv hyp := try (inversion hyp; fail).

Lemma eqb_refl : forall n m, Nat.eqb n m = true <-> n = m.
Proof.
  intros. split; intros.
  + revert m H. induction n; destruct m; intros;
    simpl in *; refl; tinv H.
    replace m with n; refl. exact (IHn m H).
  + subst. induction m; eauto.
Qed.

Lemma eqb_false_refl : forall n m, Nat.eqb n m = false <-> n <> m.
Proof.
  intros. split; intros.
  + intro Hcontra. apply eqb_refl in Hcontra.
    rewrite Hcontra in H; tinv H.
  + destruct (Nat.eqb n m) eqn: EQ; refl. apply eqb_refl in EQ.
    destruct (H EQ).
Qed.

Lemma leb_refl : forall n m, Nat.leb n m = true <-> n <= m.
Proof.
  intros; split; revert m.
  + induction n; intros.
    - induction m; eauto.
    - induction m; tinv H. specialize (IHn m H). clear H IHm.
      apply le_prog; eauto.
  + induction n; intros.
    - clear H. induction m; eauto.
    - induction m; tinv H.
      simpl. inversion H.
      * clear n IHn H IHm H1. induction m; eauto.
      * clear m0 H0. specialize (IHm H1). clear H H1 IHn.
        revert n m IHm. induction n; induction m; eauto.
Qed.

Lemma leb_false_refl : forall n m, Nat.leb n m = false <-> n > m.
Proof.
  intros; split; revert m.
  + induction n; intros.
    - simpl in H; tinv H.
    - induction m.
      * clear IHn H. unfold gt. apply leb_refl; eauto.
      * specialize (IHn m H). unfold gt in *. unfold lt in *.
        apply le_prog; eauto.
  + induction n; intros; tinv H.
    induction m; refl. simpl in *. unfold gt in *. unfold lt in *.
    apply leb_refl in H.
    replace (Nat.leb (S (S m)) (S n)) with (Nat.leb (S m) n) in H by refl.
    apply leb_refl in H. exact (IHn m H).
Qed.

Lemma ltb_refl : forall n m, Nat.ltb n m = true <-> n < m.
Proof.
  split; intros; apply leb_refl; eauto.
Qed.

Lemma ltb_false_refl : forall n m, Nat.ltb n m = false <-> n >= m.
Proof.
  split; intros.
  + unfold Nat.ltb in H. apply leb_false_refl in H. unfold ge.
    unfold gt in H. unfold lt in H. revert n m H.
    induction n; induction m; intros.
    - eauto.
    - inversion H. inversion H1.
    - clear IHn H. induction n; eauto.
    - inversion H; eauto.
  + unfold ge in H. unfold Nat.ltb. apply leb_false_refl. unfold gt.
    apply le_prog; eauto.
Qed.

Ltac bdestruct b :=
  destruct b eqn: ?;
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply eqb_refl in H
  | H : Nat.leb _ _ = true |- _ => apply leb_refl in H
  | H : Nat.ltb _ _ = true |- _ => apply ltb_refl in H
  | H : Nat.eqb _ _ = false |- _ => apply eqb_false_refl in H
  | H : Nat.leb _ _ = false |- _ => apply leb_false_refl in H
  | H : Nat.ltb _ _ = false |- _ => apply ltb_false_refl in H
  end
.

Lemma split_crit : forall n m, n < m \/ n = m \/ n > m.
Proof.
  intros. bdestruct (Nat.ltb n m); eauto. right.
  bdestruct (Nat.ltb m n); eauto. left.
  unfold ge in *. repeat match goal with
  | H : _ <= _ |- _ => apply leb_refl in H
  end. revert m Heqb Heqb0; induction n; destruct m; intros; refl.
  + tinv Heqb.
  + tinv Heqb0.
  + simpl in *. specialize (IHn m Heqb Heqb0). subst; refl.
Qed.

