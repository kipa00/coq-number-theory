Require Export division.

Definition composite (n : nat) : Prop :=
  exists x y, x > 1 /\ y > 1 /\ x * y = n.

Definition prime (n : nat) : Prop :=
  n > 1 /\ ~composite n.

Fixpoint naive_is_prime' (n : nat) (m : nat) : bool :=
  match m with
  | 0 => false
  | S m' => match m' with
    | 0 => true
    | S m'' => if Nat.eqb (Nat.modulo n m) 0 then false
               else naive_is_prime' n m'
    end
  end
.

Definition naive_is_prime (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => naive_is_prime' n n'
  end
.

Lemma modulo_refl : forall n m, m > 0 ->
  Nat.modulo n m = 0 <-> exists k, n = m * k.
Proof.
  intros; split; intros.
  + exists (Nat.div n m).
    assert (FACT := div_modulo_eq n m H). rewrite H0 in FACT.
    rewrite plus_comm in FACT. simpl in FACT. rewrite mul_comm. assumption.
  + destruct H0 as [k Heqk].
    assert (FACT := division_uniq n m H).
    assert (FACTlt := modulo_less n m H).
    assert (FACTeq := div_modulo_eq n m H).
    destruct FACT as [q [r [_ [_ FACT]]]]. rewrite mul_comm in FACTeq. 
    destruct (FACT _ _ FACTlt FACTeq) as [Heqq Heqr].
    replace (m * k) with (m * k + 0) in Heqk by (apply plus_comm; eauto).
    destruct (FACT k 0 H Heqk) as [Heqq2 Heqr2].
    rewrite <- Heqr; assumption.
Qed.

Lemma prime_then_nprime' : forall n m, 0 < m < n -> prime n
  -> naive_is_prime' n m = true.
Proof.
  intros n m Hlt Hpr. destruct n; try destruct n.
  + destruct Hpr. inversion H.
  + destruct Hpr. inversion H. inversion H2.
  + induction m; try (destruct Hlt; inversion H; fail).
    remember (S (S n)) as SSn. unfold naive_is_prime'.
    fold naive_is_prime'. destruct m; eauto.
    bdestruct (Nat.eqb (Nat.modulo SSn (S (S m))) 0).
    - assert (S (S m) > 0). { clear. induction m; eauto. }
      assert (S (S m) > 1). { clear. induction m; eauto. }
      apply (modulo_refl SSn (S (S m))) in Heqb; try assumption.
      destruct Heqb as [k Heqk]. destruct k; try destruct k.
      * rewrite mul_comm in Heqk; simpl in Heqk. subst. inversion Heqk.
      * rewrite mul_comm in Heqk; simpl in Heqk.
        rewrite (plus_comm m 0) in Heqk. simpl in Heqk.
        rewrite <- Heqk in Hlt. destruct Hlt.
        assert (forall n, n < n -> False). {
          clear. intros n Hn. induction n; try (inversion Hn; fail).
          apply le_rev in Hn. exact (IHn Hn).
        } apply H3 in H2. inversion H2.
      * assert (composite SSn). {
          exists (S (S m)), (S (S k)).
          split; try split; try assumption; try congruence.
          clear. induction k; eauto.
        } destruct Hpr as [_ Hpr]. destruct (Hpr H1).
    - apply IHm. clear IHm Heqb Hpr. subst. split.
      * clear. induction m; eauto.
      * destruct Hlt as [_ Hlt]. unfold lt in *.
        apply le_rev in Hlt. eauto.
Qed.

Lemma prime_then_nprime : forall n, prime n -> naive_is_prime n = true.
Proof.
  intros n Hpr. destruct n; try destruct n.
  + destruct Hpr; inversion H.
  + destruct Hpr; inversion H. inversion H2.
  + remember (S (S n)) as SSn. unfold naive_is_prime. subst.
    apply prime_then_nprime'; try assumption.
    split; eauto. clear. induction n; eauto.
Qed.

Lemma nprime'_refl : forall n m, naive_is_prime' n m = true ->
  forall k, (1 < k <= m -> forall x, n <> k * x).
Proof.
  intros n m; revert n; induction m; intros.
  + destruct H0 as [_ H0]. inversion H0. intro Hcontra.
    simpl in Hcontra. subst. simpl in H. inversion H.
  + destruct H0 as [Hgt Hlt].
    unfold naive_is_prime' in H. fold naive_is_prime' in H.
    destruct m.
    - apply ltb_refl in Hgt. apply ltb_false_refl in Hlt.
      rewrite Hlt in Hgt; inversion Hgt.
    - bdestruct (Nat.eqb (Nat.modulo n (S (S m))) 0);
      try (inversion H; fail). inversion Hlt.
      * clear Hlt. assert (~(exists x, n = (S (S m)) * x)). {
          intro Hcontra.
          assert (S (S m) > 0). { clear. induction m; eauto. }
          apply modulo_refl in Hcontra; try assumption.
          destruct (Heqb Hcontra).
        } intro Hcontra. assert (exists x, n = S (S m) * x). {
          exists x; assumption.
        } destruct (H1 H2).
      * clear m0 H0 Hlt. exact (IHm n H k (conj Hgt H1) x).
Qed.

Lemma le_zero : forall x y, x + y <= x -> y = 0.
Proof.
  intros x. destruct y; refl.
  revert x. induction y; intros.
  + apply leb_refl in H. induction x; eauto. simpl in H. inversion H.
  + apply le_S in H. rewrite plus_comm in H. simpl in H.
    apply le_rev in H. replace (S (y + x)) with (x + S y) in H by (
      rewrite (plus_comm x (S y)); eauto
    ). specialize (IHy x H). inversion IHy.
Qed.

Lemma nprime_then_prime : forall n, naive_is_prime n = true -> prime n.
Proof.
  intros. destruct n; try destruct n; try (inversion H; fail).
  split; try (clear; induction n; eauto; fail). intro Hcontra.
  destruct Hcontra as [x [y [Hgtx [Hgty Heq]]]].
  unfold naive_is_prime in H.
  assert (Hstep := nprime'_refl _ _ H).
  bdestruct (Nat.ltb x (S (S n))).
  + unfold gt in Hgtx. apply le_rev in Heqb.
    specialize (Hstep x (conj Hgtx Heqb) y).
    rewrite Heq in Hstep.
    assert (S (S n) = S (S n)). { refl. } destruct (Hstep H0).
  + destruct y; try destruct y.
    - inversion Hgty.
    - inversion Hgty. inversion H1.
    - rewrite mul_comm in Heq. simpl in Heq.
      rewrite <- Heq in Heqb. apply le_zero in Heqb.
      destruct x; try (inversion Hgtx; fail).
      simpl in Heqb. inversion Heqb.
Qed.

Theorem naive_prime_refl : forall n, prime n <-> naive_is_prime n = true.
Proof.
  intros; split; intros.
  + apply prime_then_nprime; assumption.
  + apply nprime_then_prime; assumption.
Qed.

Lemma nnprime'_then_composite : forall n m, 0 < m < n
  -> naive_is_prime' n m = false -> composite n.
Proof.
  intros n m; revert n. induction m; intros.
  + destruct H as [H _]. inversion H.
  + destruct H as [Hgtm H]. unfold naive_is_prime' in H0.
    fold naive_is_prime' in H0. destruct m; try (inversion H0; fail).
    bdestruct (Nat.eqb (Nat.modulo n (S (S m))) 0).
    - clear H0. assert (S (S m) > 0). { clear. induction m; eauto. }
      apply modulo_refl in Heqb; try assumption. destruct Heqb as [k Heqk].
      destruct k; try destruct k.
      * rewrite mul_comm in Heqk. simpl in Heqk. subst. inversion H.
      * rewrite mul_comm in Heqk. simpl in Heqk.
        rewrite plus_comm in Heqk. simpl in Heqk.
        rewrite Heqk in H. repeat apply le_rev in H.
        clear IHm Hgtm Heqk H0. induction m;
        try (inversion H; fail). apply le_rev in H. eauto.
      * assert (forall u, S (S u) > 1). { clear. induction u; eauto. }
        exists (S (S m)), (S (S k)). split; try split; eauto.
    - clear Heqb. apply le_S in H. apply le_rev in H. clear Hgtm.
      assert (0 < S m). { clear; induction m; eauto. }
      exact (IHm n (conj H1 H) H0).
Qed.

Lemma nnprime_then_composite : forall n, n > 1 -> naive_is_prime n = false
  -> composite n.
Proof.
  intros. destruct n; try (inversion H; fail).
  destruct n; try (inversion H; inversion H2; fail).
  clear H. unfold naive_is_prime in H0.
  assert (0 < S n < S (S n)). { 
    split.
    + clear; induction n; eauto.
    + apply le_n.
  } apply (nnprime'_then_composite _ (S n)); assumption.
Qed.

Theorem excluded_middle_prime : forall n, n > 1 -> prime n \/ composite n.
Proof.
  intros. destruct (naive_is_prime n) eqn: EQ.
  + left. apply naive_prime_refl in EQ. assumption.
  + right. apply nnprime_then_composite; assumption.
Qed.
