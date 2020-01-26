Require Export division.

Definition square (n : nat) : nat := n * n.

Lemma sq_expand : forall n, square n >= n.
Proof.
  destruct n; try destruct n; eauto. unfold square.
  simpl. repeat apply le_prog. remember (S (S (n + n * (S (S n))))) as k.
  clear. rewrite (plus_comm n k). induction k; simpl; eauto.
Qed.

Lemma sq_inc' : forall n, square n < square (S n).
Proof.
  intros; unfold square. simpl_arith.
  replace (S (n + (n + n * n))) with (S n + (n + n * n)) by eauto.
  rewrite (plus_comm (S _) _). rewrite (plus_comm n (n * n)).
  rewrite <- plus_assoc. remember (n * n) as x. rewrite <- plus_n_Sm.
  remember (n + n) as y. clear. rewrite plus_comm. simpl. apply le_prog.
  induction y; simpl; eauto.
Qed.

Lemma sq_inc : forall x y, x <= y -> square x <= square y.
Proof.
  intros x y; revert x. induction y; intros.
  + inversion H; subst; eauto.
  + inversion H; eauto. clear H H0 m. specialize (IHy x H1).
    eapply le_trans; try eassumption. apply le_rev; apply le_S.
    apply sq_inc'.
Qed.

Lemma sq_inc_strong : forall x y, x < y -> square x < square y.
Proof.
  intros x y; revert x. induction y; intros.
  + inversion H.
  + inversion H.
    - apply sq_inc'.
    - clear H H0 m. specialize (IHy x H1).
    eapply le_trans; try eassumption. apply le_rev; apply le_S.
    apply sq_inc'.
Qed.

Lemma sq_inj : forall x y, square x = square y -> x = y.
Proof.
  intros. destruct (split_crit x y) as [Hb | [Hb | Hb]]; try assumption;
  apply sq_inc_strong in Hb; rewrite H in Hb; destruct (le_contra _ 0 Hb).
Qed.

Lemma sq_mod_four : forall x,
  Nat.modulo (square x) 4 = 0 \/ Nat.modulo (square x) 4 = 1.
Proof.
  intros. eassert (4 > 0) by (apply ltb_refl; eauto).
  destruct (division_uniq x 4 H) as [q [r [Hltr [Heq Huniq]]]].
  destruct (division_uniq (square x) 4 H)
    as [q' [r' [Hltr' [Heqsq Huniq']]]].
  assert (FACT :
    square x = 4 * Nat.div (square x) 4
    + Nat.modulo (square x) 4
  ). {
    assert (Hi := div_modulo_eq (square x) _ H). rewrite (mul_comm 4 _).
    assumption.
  } destruct r; try destruct r; try destruct r; try destruct r.
  + replace (4 * q + 0) with (4 * q) in Heq by (simpl_arith; eauto).
    assert (square x = 4 * (q * (4 * q)) + 0). {
      unfold square. subst x. rewrite <- mul_assoc. simpl_arith; refl.
    } destruct (Huniq' _ _ H H0). subst q' r'.
    destruct (Huniq' _ _ (modulo_less _ _ H) FACT).
    left; congruence.
  + assert (exists qq, square x = 4 * qq + 1). {
      eexists. unfold square; subst x.
      rewrite plus_mul_dist. rewrite (mul_comm _ (4 * q)).
      rewrite plus_mul_dist. rewrite (mul_comm (4 * q + 1) 1).
      replace (1 * (4 * q + 1)) with (4 * q + 1) by (
        simpl; simpl_arith; refl
      ). repeat rewrite <- mul_assoc. rewrite <- plus_mul_dist.
      rewrite plus_assoc. rewrite <- plus_mul_dist. eauto.
    } destruct H0 as [qq Hqq].
    destruct (Huniq' _ _ Hltr Hqq); subst q' r'.
    destruct (Huniq' _ _ (modulo_less _ _ H) FACT).
    right; congruence.
  + remember 4 as z. replace 2 with (2 * 1) in Heq by refl; subst z.
    replace 4 with (2 * 2) in Heq by refl. rewrite <- mul_assoc in Heq.
    rewrite <- plus_mul_dist in Heq.
    assert (exists qq, square x = 4 * qq + 0). {
      eexists. unfold square. subst x. rewrite mul_assoc.
      rewrite <- (mul_assoc 2 _ 2). rewrite (mul_comm _ 2).
      rewrite mul_assoc. replace (2 * 2) with 4 by refl.
      rewrite <- mul_assoc. eauto.
    } destruct H0 as [qq Hqq].
    destruct (Huniq' _ _ H Hqq); subst q' r'.
    destruct (Huniq' _ _ (modulo_less _ _ H) FACT).
    left; congruence.
  + eassert (H1lt4 : 1 < 4) by (apply ltb_refl; eauto).
    assert (exists qq, square x = 4 * qq + 1). {
      eexists. unfold square. subst x.
      rewrite plus_mul_dist. rewrite (mul_comm _ (4 * q)).
      rewrite plus_mul_dist. rewrite (mul_comm (4 * q + 3) 3).
      rewrite plus_mul_dist. replace (3 * 3) with (4 * 2 + 1) by refl.
      repeat rewrite plus_assoc.
      (* first *) replace (4 * q * (4 * q)) with (4 * (q * 4 * q)) by (
        repeat rewrite mul_assoc; refl
      ). (* second *) replace (4 * q * 3) with (4 * (q * 3)) by (
        repeat rewrite mul_assoc; refl
      ). (* third *) replace (3 * (4 * q)) with (4 * (3 * q)) by (
        repeat rewrite mul_assoc; refl
      ). repeat rewrite <- (plus_mul_dist 4). eauto.
    } destruct H0 as [qq Hqq].
    destruct (Huniq' _ _ H1lt4 Hqq); subst q' r'.
    destruct (Huniq' _ _ (modulo_less _ _ H) FACT).
    right; congruence.
  + repeat apply le_rev in Hltr. tinv Hltr.
Qed.
