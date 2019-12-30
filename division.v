Require Export refl.

Lemma sub_nonzero : forall x y, S x - y <> 0 -> S x - y = S (x - y).
Proof.
  intros x. induction x.
  + destruct y; intros; eauto. assert (1 - S y = 0). {
      destruct y; eauto.
    } destruct (H H0).
  + intros. destruct y; eauto.
Qed.

Lemma sub_zero : forall x y, S x - y = 0 -> x - y = 0.
Proof.
  intros x. induction x.
  + destruct y; intros; eauto.
  + intros. destruct y; eauto. clear IHx. simpl in *. inversion H.
Qed.

Lemma modulo_less : forall n m, m > 0 -> Nat.modulo n m < m.
Proof.
  intros. unfold Nat.modulo.
  destruct m; tinv H. clear H.
  remember (snd (Nat.divmod n m 0 m)) as x. clear n Heqx.
  induction x; destruct m; eauto.
  simpl. apply ltb_refl in IHx. bdestruct (Nat.eqb (S m - x) 0).
  + apply sub_zero in Heqb. rewrite Heqb. clear x IHx Heqb.
    induction m; eauto.
  + apply sub_nonzero in Heqb. rewrite Heqb in IHx; clear Heqb.
    apply ltb_refl in IHx.
    replace (Nat.ltb (S (m - x)) (S (S m))) with (
      Nat.ltb (m - x) (S m)
    ) in IHx.
    - apply ltb_refl in IHx. eauto.
    - unfold Nat.ltb. eauto.
Qed.

Lemma divmod_eq : forall n m q r, r <= m -> 
  n + q * (S m) + (m - r) =
  match Nat.divmod n m q r with
  | (q', r') => q' * (S m) + (m - r')
  end
.
Proof.
  intros n. induction n; try (eauto; fail).
  intros. destruct r.
  + simpl. specialize (IHn m (S q) m). rewrite <- IHn; try (eauto; fail).
    clear IHn H. rewrite <- (plus_assoc _ _ (_ - 0)).
    rewrite (plus_comm _ (_ - 0)).
    replace (m - 0) with m by (induction m; eauto).
    rewrite plus_assoc. rewrite (plus_comm n m).
    replace (S (m + n + q * S m)) with (S m + n + q * S m) by eauto.
    rewrite (plus_comm (S m) n). rewrite <- (plus_assoc _ _ (_ * _)).
    replace (S m + q * S m) with (S q * S m).
    - replace (m - m) with 0 by (induction m; eauto).
      rewrite (plus_comm _ 0); reflexivity.
    - replace (S m + q * S m) with (S m * 1 + q * S m).
      * rewrite (mul_comm q (S m)). rewrite <- plus_mul_dist.
        apply mul_comm; eauto.
      * rewrite (mul_comm _ 1). replace (1 * S m) with (S m) by (
          simpl; rewrite plus_comm; eauto
        ). eauto.
  + simpl. specialize (IHn m q r). assert (r <= m). {
      apply leb_refl in H. destruct m.
      - inversion H.
      - simpl in H. apply leb_refl in H. eauto.
    } specialize (IHn H0). rewrite <- IHn. clear H0 IHn.
    replace (S (n + q * S m + (m - S r))) with (n + q * S m + S (m - S r)).
    - replace (S (m - S r)) with (S m - S r); try (eauto; fail). 
      clear n q. remember (S r) as n. clear Heqn r. apply sub_nonzero.
      intro Hcontra. apply leb_refl in H. revert n m H Hcontra.
      intro n. induction n; intros m Hleb Hcontra;
      try (inversion Hcontra; fail). simpl in Hcontra. destruct m;
      try (inversion Hleb; fail). simpl in Hleb.
      destruct (IHn m Hleb Hcontra).
    - rewrite <- (plus_assoc _ _ (S _)).
      rewrite (plus_comm (_ * _) (S _)). rewrite plus_assoc.
      rewrite (plus_comm n (S _)).
      replace (S (m - S r) + n + q * S m) with (
        S ((m - S r) + n + q * S m)
      ) by eauto. rewrite (plus_comm _ n).
      rewrite <- (plus_assoc _ (_ - _) _). rewrite (plus_comm (_ - _) _).
      rewrite plus_assoc. eauto.
Qed.

Lemma div_modulo_eq : forall n m, m > 0 ->
  n = (Nat.div n m) * m + (Nat.modulo n m).
Proof.
  intros. unfold Nat.div. unfold Nat.modulo.
  destruct m; try (unfold gt in H; apply ltb_refl in H; inversion H).
  destruct (Nat.divmod n m 0 m) eqn: EQ. simpl.
  clear H. assert (ult := divmod_eq n m 0 m). rewrite EQ in ult.
  rewrite <- ult; eauto.
  clear n0 n1 EQ ult. simpl.
  replace (m - m) with 0 by (induction m; eauto).
  rewrite <- plus_assoc; simpl. rewrite plus_comm; eauto.
Qed.

Fixpoint div_intui' (fuel : nat)
  (n : nat) (m : nat) (q : nat) : nat * nat :=
  match fuel with
  | 0 => (0, 0)
  | S fuel' => if Nat.ltb n m then (q, n) else
               div_intui' fuel' (n - m) m (S q)
  end
.

Definition div_intui (n : nat) (m : nat) : nat * nat :=
  div_intui' (S n) n m 0.

Lemma div_intui'_less : forall fuel n m q, fuel > n -> m > 0 ->
  match div_intui' fuel n m q with
  | (q, r) => r
  end < m.
Proof.
  intro fuel. induction fuel; eauto.
  simpl. intros. bdestruct (Nat.ltb n m); try assumption.
  apply IHfuel; try assumption; clear IHfuel.
  destruct m; try (inversion H0; fail).
  unfold gt in *. inversion H; subst; clear H.
  + destruct fuel; try (inversion Heqb; fail). simpl.
    clear q H0 Heqb. revert fuel; induction m.
    - intros; simpl. destruct fuel; eauto.
    - intros. destruct fuel; eauto. simpl. specialize (IHm fuel). eauto.
  + clear H0. unfold ge in *. unfold lt in *. clear Heqb q.
    remember (S m) as m'. clear Heqm' m. rename m' into m.
    induction m; destruct n; eauto.
    simpl. bdestruct (Nat.eqb (S n - m) 0).
    - rewrite Heqb in IHm. apply sub_zero in Heqb. rewrite Heqb. eauto.
    - apply sub_nonzero in Heqb. rewrite Heqb in *. clear H2 Heqb.
      remember (n - m) as x. clear n m Heqx. rename fuel into y.
      inversion IHm; subst; clear IHm; eauto.
      destruct m; try destruct m; try (inversion H; fail).
      * inversion H. inversion H1.
      * apply le_prog. repeat apply le_rev in H. eauto.
Qed.

Lemma div_intui'_eq : forall fuel n m q, fuel > n -> m > 0 ->
  n + m * q = match div_intui' fuel n m q with
  | (q, r) => m * q + r
  end
.
Proof.
  intro fuel; induction fuel; intros.
  + inversion H.
  + simpl. bdestruct (Nat.ltb n m).
    - apply plus_comm; refl.
    - specialize (IHfuel (n - m) m (S q)). assert (n - m + m = n). {
        clear IHfuel fuel q H H0. revert n Heqb.
        induction m; try (intros; induction n; eauto; fail).
        intros n H. destruct n; tinv H. apply le_rev in H.
        specialize (IHm n H). simpl. rewrite plus_comm. simpl.
        rewrite plus_comm. rewrite IHm; refl.
      } assert (fuel > n - m). {
        unfold gt in *. unfold lt in *.
        destruct m; try (inversion H0; fail). destruct n;
        try (inversion Heqb; fail). clear H0 H1 IHfuel Heqb. simpl.
        apply le_rev in H. clear q. revert fuel n H. induction m; intros;
        try (destruct n; assumption). destruct n; try assumption. simpl.
        specialize (IHm fuel n). destruct fuel; try (inversion H; fail).
        apply le_rev in H. apply le_S in H. exact (IHm H).
      } specialize (IHfuel H2 H0). clear H2. rewrite <- IHfuel.
      clear fuel IHfuel H H0 Heqb. rewrite (mul_comm _ (S _)). simpl.
      rewrite (mul_comm _ m). rewrite plus_assoc. rewrite H1; refl.
Qed.

Lemma add_false : forall m x, m + x < m -> False.
Proof.
  intros m x; revert m. induction x.
  + intros. rewrite plus_comm in H. simpl in H. apply ltb_refl in H.
    induction m; try (inversion H; fail). exact (IHm H).
  + intros. rewrite plus_comm in H. simpl in H. rewrite plus_comm in H.
    replace (S (m + x)) with (S m + x) in H by eauto. apply le_S in H.
    destruct (IHx _ H).
Qed.

Lemma div_uniq' : forall n m, m > 0 -> (
  forall q r q' r', r < m -> r' < m -> n = m * q + r -> n = m * q' + r'
    -> q = q' /\ r = r'
  )
.
Proof.
  intro n. remember (
    fun n =>
      forall m : nat, m > 0 -> forall q r q' r' : nat,
        r < m -> r' < m -> n = m * q + r -> n = m * q' + r'
        -> q = q' /\ r = r'
  ) as P. replace (
    forall m : nat, m > 0 -> forall q r q' r' : nat,
      r < m -> r' < m -> n = m * q + r -> n = m * q' + r'
      -> q = q' /\ r = r'
  ) with (P n) by (subst; eauto). revert n. apply strong_natind.
  subst; intros. bdestruct (Nat.ltb n m).
  + destruct m; try (inversion H0; fail). clear H0.
    destruct q.
    - destruct q'.
      * split; eauto. rewrite (mul_comm (S m) 0) in *. simpl in *.
        subst; eauto.
      * rewrite mul_comm in H4. remember (S m) as m'. simpl in H4.
        subst m'. rewrite <- plus_assoc in H4. rewrite H4 in Heqb.
        apply add_false in Heqb. destruct Heqb.
    - remember (S m) as m'. rewrite mul_comm in H3. simpl in H3.
      rewrite <- plus_assoc in H3. rewrite H3 in Heqb.
      apply add_false in Heqb. destruct Heqb.
  + assert (forall n m, m > 0 -> n >= m -> n - m < n). {
      clear. intros. destruct m; try (inversion H; fail). clear H.
      revert m H0. induction n.
      - intros. inversion H0.
      - intros. apply le_rev in H0. simpl. destruct m.
        * replace (n - 0) with n by (clear; induction n; eauto). eauto.
        * specialize (IHn m H0). exact (le_S _ _ IHn).
    } specialize (H (n - m) (H5 _ _ H0 Heqb) m H0). clear H5. destruct q.
    - rewrite mul_comm in H3. simpl in H3. subst n. apply ltb_refl in H1.
      apply ltb_false_refl in Heqb. rewrite H1 in Heqb. inversion Heqb.
    - destruct q'.
      * rewrite mul_comm in H4. simpl in H4. clear H3. subst n.
        apply ltb_refl in H2. apply ltb_false_refl in Heqb.
        rewrite H2 in Heqb. inversion Heqb.
      * assert (n - m = m * q + r). {
          clear H H0 q' r' H1 H2 H4. rename H3 into H.
          rewrite mul_comm in H. simpl in H. assert (
            n - m = (m + q * m + r) - m
          ). { subst; eauto. }
          rewrite <- plus_assoc in H0. rewrite plus_minus_cancel in H0.
          rewrite H0. clear. rewrite mul_comm. refl.
        } assert (n - m = m * q' + r'). {
          clear H H0 q r H1 H2 H3 H5. rename H4 into H.
          rewrite mul_comm in H. simpl in H. assert (
            n - m = (m + q' * m + r') - m
          ). { subst; eauto. } clear H; rename H0 into H.
          rewrite <- plus_assoc in H. rewrite plus_minus_cancel in H.
          rewrite mul_comm in H. assumption.
        } destruct (H q r q' r' H1 H2 H5 H6) as [Hq Hr]. split; eauto.
Qed.

Lemma division_uniq : forall n m, m > 0 ->
  exists q r, r < m /\ n = m * q + r /\ forall q' r',
    r' < m -> n = m * q' + r' -> q = q' /\ r = r'.
Proof.
  intros. destruct (div_intui n m) as [q r] eqn: EQ.
  exists q, r. unfold div_intui in EQ.
  split; try split.
  + assert (EXACT := div_intui'_less (S n) n m 0 (le_n (S n)) H).
    rewrite EQ in EXACT. exact EXACT.
  + assert (EXACT := div_intui'_eq (S n) n m 0 (le_n (S n)) H).
    rewrite (mul_comm _ 0) in EXACT. replace (n + 0 * m) with n in EXACT
    by (
      simpl; rewrite plus_comm; refl
    ). rewrite EQ in EXACT. exact EXACT.
  + intros. assert (EXACT := div_uniq' n m H q r q' r').
    assert (Hrltm := div_intui'_less (S n) n m 0 (le_n (S n)) H).
    rewrite EQ in Hrltm.
    assert (Heq := div_intui'_eq (S n) n m 0 (le_n (S n)) H).
    rewrite (mul_comm m 0) in Heq. rewrite plus_comm in Heq.
    rewrite EQ in Heq. simpl in Heq.
    exact (EXACT Hrltm H0 Heq H1).
Qed.
